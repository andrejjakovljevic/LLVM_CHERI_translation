#include "llvm/Pass.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/MDBuilder.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <string>
#include <map>

using namespace llvm;

namespace {
struct Hello : public ModulePass {
  static char ID;
  Hello() : ModulePass(ID) {}

  template<typename T>
  void ReplaceUnsafe(T *from, T *to) 
  {
    std::vector<Use*> uses_to_fix; 
    auto con_from = dyn_cast<Constant>(from);
    auto con_to = dyn_cast<Constant>(to);
    if (con_from && con_to)
    {
      change_all_aliases(con_from, con_to);
    }
    while (!from->use_empty()) {
      auto &U = *from->use_begin();
      if (isa<Constant>(U.getUser())) 
      {
        uses_to_fix.push_back(&U);
      }
      U.set(to);
    }
    for (Use* u : uses_to_fix)
    {
      u->set(from);
    }
  }


  std::unordered_map<StructType*,StructType*> struct_map_mapping;
  std::unordered_map<StructType*,bool> has_pointer_map;
  std::unordered_set<StructType*> new_structs;
  std::map<GlobalVariable*,GlobalVariable*> old_to_new_variable;
  Module* whole_module;

  std::unordered_map<Function*,Function*> fake_to_real_functions;
  std::unordered_map<Function*,Function*> real_to_fake_functions;
  std::unordered_map<BasicBlock*,BasicBlock*>  fake_to_real_basicBlocks;
  std::unordered_map<BasicBlock*,BasicBlock*>  real_to_fake_basicBlocks;
  std::unordered_map<Function*,FunctionType*> new_ft_of_function;
  std::unordered_set<Function*> functions_to_fix_later;
  std::unordered_map<Constant*, std::vector<GlobalAlias*>> map_const_to_alias;
  std::unordered_set<GlobalVariable*> already_changed_global_variables;
  std::unordered_set<Function*> changed_functions_for_vararg;
  std::unordered_map<Function*, std::unordered_set<int>> old_changed_for_va_arguments;

  bool ends_with(std::string const & value, std::string const & ending)
  {
      if (ending.size() > value.size()) return false;
      return std::equal(ending.rbegin(), ending.rend(), value.rbegin());
  }


  int get_size_from_string(std::string name, bool is_cheri)
  {
    auto split = split_string(name," ");
    // if it is struct
    if (StructType* st = StructType::getTypeByName(whole_module->getContext(),"struct."+split[1]))
    {
      if (split[split.size()-1]=="*" || is_prefix(split[split.size()-1],"*")) 
      {
        if (is_cheri) return 16;
        else return 8;
      }
      else
      {
        int new_size = struct_type_size(st,is_cheri);
        return new_size;
      }
    }
    // could be a union
    if (StructType* st = StructType::getTypeByName(whole_module->getContext(),"union."+split[1]))
    {
      if (split[split.size()-1]=="*" || is_prefix(split[split.size()-1],"*")) 
      {
        if (is_cheri) return 16;
        else return 8;
      }
      else
      {
        int new_size = struct_type_size(st,is_cheri);
        return new_size;
      }
    }
    else if (split[split.size()-1]=="*")
    {
      if (is_cheri) return 16;
      else return 8;
    }
    else return -1;
  }

  bool does_field_need_alignment(StructType* struct_type, int curr_pos)
  {
    if (curr_pos==0)
    {
      if (get_alignment_is_higher(struct_type))
      {
        return true;
      }
      else return false;
    }
    else
    {
      if (curr_pos-1<struct_type->getNumElements())
      {
        Type* t = struct_type->getElementType(curr_pos-1);
        if (get_alignment_is_higher(t))
        {
          return true;
        }
        else return false;
      }
    }
    return false;
  }

  bool check_if_pointer_type_to_va_list(PointerType* pt_ty)
  {
    Type* elem_type = pt_ty->getElementType();
    if (auto st_ty = dyn_cast<StructType>(elem_type))
    {
      if (!st_ty->isLiteral() && st_ty->getName().str()=="struct.__va_list")
      {
        return true;
      }
      else return false;
    }
    else if (auto po_ty = dyn_cast<PointerType>(elem_type))
    {
      return check_if_pointer_type_to_va_list(po_ty);
    }
    else return false;
  }

  Type* change_from_va_type(Type* type_to_change)
  {
    if (auto st_ty = dyn_cast<StructType>(type_to_change))
    {
      auto i8_type = Type::getInt8Ty(whole_module->getContext());
      return i8_type;
    }
    else if (auto po_ty = dyn_cast<PointerType>(type_to_change))
    {
      return PointerType::get(change_from_va_type(po_ty->getElementType()),200);
    }
    return type_to_change;
  }

  std::unordered_map<Type*, Type*> types_global_va;

  Type* change_from_va_type_for_globals(Type* type_to_change)
  {
    if (types_global_va.find(type_to_change)!=types_global_va.end())
    {
      return types_global_va[type_to_change];
    }
    if (type_to_change->isStructTy())
    {
      bool sol=false;
      StructType* sType = dyn_cast<StructType>(type_to_change);
      if (sType->getName().str()=="struct.__va_list")
      {
        auto i8_type = Type::getInt8Ty(whole_module->getContext());
        return PointerType::get(i8_type,200);
      }
      std::vector<Type*> types;
      for (auto& elem_type : sType->elements())
      {
        types.push_back(change_from_va_type_for_globals(elem_type));
      }
      ArrayRef<Type*> new_struct_types(types); 
      StructType* new_struct;
      if (sType->isLiteral()) 
      {
        new_struct = StructType::get(whole_module->getContext(), new_struct_types, sType->isPacked());
      }
      else
      {
        auto name = sType->getName().str();
        sType->setName("");
        new_struct = StructType::create(new_struct_types,name,sType->isPacked());
      }

      types_global_va[type_to_change] = new_struct;
      return types_global_va[type_to_change];
    }
    else if (type_to_change->isArrayTy())
    {
      auto* AT = dyn_cast<ArrayType>(type_to_change);
      types_global_va[type_to_change] = ArrayType::get(change_from_va_type_for_globals(AT->getElementType()), AT->getNumElements());
      return types_global_va[type_to_change];
    }
    else if (type_to_change->isPointerTy())
    {
      auto* PT = dyn_cast<PointerType>(type_to_change);
      types_global_va[type_to_change] = PointerType::get(change_from_va_type_for_globals(PT->getElementType()),200);
      return types_global_va[type_to_change];
    }
    else return type_to_change;
  }

  GlobalVariable* change_global_variable_for_va_arg(GlobalVariable* global)
  {
    Type* new_type = change_from_va_type_for_globals(global->getType());
    auto name_global = global->getName().str();
    global->setName("");
    Constant* initializer = nullptr;
    if (global->getInitializer()->isZeroValue())
    {
      initializer = Constant::getNullValue(((PointerType*)new_type)->getElementType());
    }
    GlobalVariable* test_gv = new GlobalVariable(*global->getParent(), ((PointerType*)new_type)->getElementType(), global->isConstant(), global->getLinkage(), initializer, name_global, global, global->getThreadLocalMode(), 200);
    return test_gv;
  }

  std::unordered_map<Type*, bool> is_va_list;

  bool check_if_type_to_va_list_for_globals(Type* ty)
  {
    if (is_va_list.find(ty)!=is_va_list.end())
    {
      return is_va_list[ty];
    }
    is_va_list[ty]=false;
    bool ans = false;
    if (ty->isStructTy())
    {
      bool sol=false;
      StructType* sType = dyn_cast<StructType>(ty);
      if (!sType->isLiteral() && sType->getName().str()=="struct.__va_list")
      {
        ans=true;
      }
      else
      {
        sol=false;
        for (auto& elem_type : sType->elements())
        {
          sol |= check_if_type_to_va_list_for_globals(elem_type);
        }
        ans=sol;
      }
    }
    else if (ty->isArrayTy())
    {
      ans = check_if_type_to_va_list_for_globals(((ArrayType*)ty)->getElementType());
    }
    else if (ty->isPointerTy())
    {
      ans = check_if_type_to_va_list_for_globals(((PointerType*)ty)->getElementType());
    }
    else ans = false;
    is_va_list[ty] = ans;
    return ans;
  }


  int get_struct_alignment(StructType* struct_type, bool is_cheri)
  {
    int max_ali = 0;
    for (auto& elem_type : struct_type->elements())
    {
      if (max_ali<get_alignment(elem_type, is_cheri)) max_ali=get_alignment(elem_type, is_cheri);
    }
    return max_ali;
  }

  int get_array_alignment(ArrayType* array_type, bool is_cheri)
  {
    return get_alignment(array_type->getElementType(),is_cheri);
  }

  int get_alignment(Type* type, bool is_cheri)
  {
    if (auto st = dyn_cast<StructType>(type))
    {
      if (st->isPacked()) return 1;
    }
    if (type->isIntegerTy())
    {
      return type->getIntegerBitWidth()/8;
    }
    else if (type->isStructTy())
    {
      return get_struct_alignment((StructType*)type,is_cheri);
    }
    else if (type->isArrayTy())
    {
      return get_array_alignment((ArrayType*)type,is_cheri);
    }
    else if (type->isPointerTy())
    {
      if (is_cheri) return 16;
      else return 8;
    }
    else if (type->getTypeID() == Type::DoubleTyID)
    {
      return 8;
    }
    else if (type->getTypeID() == Type::FloatTyID)
    {
      return 4;
    }
    return 0;  
  }

  int array_type_size(ArrayType* array_type, bool is_cheri)
  {
    int size_of_array = array_type->getNumElements();
    Type* new_type = array_type->getElementType();
    int size_of_elem = get_size(new_type, is_cheri);
    return size_of_array*size_of_elem;
  }

  int struct_type_size(StructType* struct_type, bool is_cheri)
  {
    int res = 0;
    int overall_alignment = get_alignment(struct_type,is_cheri);
    bool is_packet = struct_type->isPacked();
    for (auto& elem_type : struct_type->elements())
    {
      int alig = get_alignment(elem_type, is_cheri);
      auto k = get_size(elem_type, is_cheri);
      res+=k;
      if (!is_packet)
      {
        if (res%alig!=0)
        {
          int for_now = res/alig;
          res=(for_now+1)*alig;
        }
      }
    }
    if (res%overall_alignment!=0)
    {
      if (!is_packet)
      {
        int for_now = res/overall_alignment;
        res=(for_now+1)*overall_alignment;
      }
    }
    return res;
  }

  int get_size(Type* type, bool is_cheri)
  {
    if (type->isIntegerTy())
    {
      return type->getIntegerBitWidth()/8;
    }
    else if (type->isStructTy())
    {
      return struct_type_size((StructType*)type,is_cheri);
    }
    else if (type->isArrayTy())
    {
      return array_type_size((ArrayType*)type,is_cheri);
    }
    else if (type->isPointerTy())
    {
      if (is_cheri) return 16;
      else return 8;
    }
    else if (type->getTypeID() == Type::DoubleTyID)
    {
      return 8;
    }
    else if (type->getTypeID() == Type::FloatTyID)
    {
      return 4;
    }
    return 0;
  }

  Type* changeStructType(Type* operandType, int targetAddressSpace)
  {
    if (auto sType = dyn_cast<StructType>(operandType)) 
    {
      // no mapping
      if (new_structs.find(sType)!=new_structs.end()) return operandType;
      // We have to create a new struct, to stop infinite recursion 
      if (struct_map_mapping.find(sType)==struct_map_mapping.end())
      {
        // We change this manually
        if (!sType->isLiteral() && sType->getName()=="union.__mbstate_t")
        {
          Type *I8PtrTy = Type::getInt8PtrTy(whole_module->getContext(), 200);
          Type *I8ArrayTy = ArrayType::get(Type::getInt8Ty(whole_module->getContext()),112);
          std::string name = "union.__mbstate_t";
          sType->setName("");
          StructType* new_struct = StructType::create(whole_module->getContext(), name);
          new_struct->setBody({I8PtrTy, I8ArrayTy});
          has_pointer_map[new_struct]=true;
          has_pointer_map[sType]=true;
          new_structs.insert(new_struct);
          struct_map_mapping[sType]=new_struct;
          return struct_map_mapping[sType];
        }
        if (!struct_has_pointer(sType))
        {
          has_pointer_map[sType]=false;
          new_structs.insert(sType);
          struct_map_mapping[sType]=sType;
          return struct_map_mapping[sType];
        }
        StructType* new_struct;
        if (!sType->isLiteral())
        {
          ArrayRef<Type*> empty;
          new_struct = StructType::create(whole_module->getContext(), "");
          struct_map_mapping[sType]=new_struct;
        }
        std::vector<Type*> types;
        bool has_pointer=false;
        for (auto& elem_type : sType->elements())
        {
          types.push_back(changeAddressSpace(elem_type,200));
          if (elem_type->isPointerTy()) has_pointer=true;
          if (elem_type->isStructTy())
          {
            auto stype2 = dyn_cast<StructType>(elem_type);
            if (has_pointer_map.find(stype2)!=has_pointer_map.end() && has_pointer_map[stype2])
            {
              has_pointer=true;
            }
          }
        }
        ArrayRef<Type*> new_struct_types(types); 
        if (sType->isLiteral()) 
        {
          new_struct = StructType::get(whole_module->getContext(), new_struct_types, sType->isPacked());
          struct_map_mapping[sType]=new_struct;
        }
        else 
        {
          auto struct_name = sType->getName().str();
          sType->setName("");
          new_struct->setName(struct_name);
          new_struct->setBody(new_struct_types);
        }
        has_pointer_map[new_struct]=has_pointer;
        has_pointer_map[sType]=has_pointer;
        new_structs.insert(new_struct);
        return struct_map_mapping[sType];
      }
      else 
      {
        return struct_map_mapping[sType];
      }
    }
    return operandType;
  }

  Type* changePointerType(Type* operandType, int targetAddressSpace)
  {
    if (auto* PT = dyn_cast<PointerType>(operandType)) 
    {
      return PointerType::get(changeAddressSpace(PT->getElementType(),targetAddressSpace),targetAddressSpace);
    }
    return operandType;
  }

  Type* changeArrayType(Type* operandType, int targetAddressSpace)
  {
    if (auto* AT = dyn_cast<ArrayType>(operandType))
    {
      if (array_has_pointer(AT))
      {
        return ArrayType::get(changeAddressSpace(AT->getElementType(),targetAddressSpace), AT->getNumElements());
      }
      else return operandType;
    } 
    return operandType;
  }

  Type* changeFunctionType(Type* operandType, int targetAddressSpace)
  {
    if (auto* functionType = dyn_cast<FunctionType>(operandType))
    {
      std::vector<Type*> new_params;
      for (int i=0;i<functionType->getNumParams();i++)
      {
        Type* old_type = functionType->getParamType(i);
        // Check if it is a type of variable argument
        bool is_va_list=false;
        if (isa<PointerType>(old_type))
        {
          auto point_type = dyn_cast<PointerType>(old_type);
          if (check_if_pointer_type_to_va_list(point_type))
          {
            Type* new_va_type = change_from_va_type(old_type);
            new_params.push_back(new_va_type);
            is_va_list=true; 
          }
        }
        if (!is_va_list) new_params.push_back(changeAddressSpace(old_type,targetAddressSpace));
      }
      Type* new_return_type = changeAddressSpace(functionType->getReturnType(),targetAddressSpace);
      ArrayRef<Type*> type_array(new_params);
      auto new_function_type = FunctionType::get(new_return_type,new_params,functionType->isVarArg());
      return new_function_type;
    }
    return operandType;
  }

  Type* changeAddressSpace(Type* operandType, int targetAddressSpace) 
  {
    if (operandType->isStructTy())
    {
      return changeStructType(operandType, targetAddressSpace);
    }
    else if (auto *PT = dyn_cast<PointerType>(operandType)) 
    {
      return changePointerType(operandType, targetAddressSpace);
    }
    else if (isa<ArrayType>(operandType))
    {
      return changeArrayType(operandType, targetAddressSpace);
    }
    else if (auto* FT = dyn_cast<FunctionType>(operandType))
    {
      return changeFunctionType(operandType, targetAddressSpace);
    }
    return operandType;
  }

  void add_module_flags(Module& M)
  {
    // Add module flags
    SmallVector<Metadata*, 4> vector_data;
    vector_data.push_back(ConstantAsMetadata::get(ConstantInt::get(Type::getInt32Ty(M.getContext()), 7)));
    vector_data.push_back(MDString::get(M.getContext(), "PIC Level"));
    vector_data.push_back(ConstantAsMetadata::get(ConstantInt::get(Type::getInt32Ty(M.getContext()), 1)));
    MDNode *node = MDNode::get(M.getContext(), vector_data);
    NamedMDNode *flags_metadata = M.getOrInsertNamedMetadata("llvm.module.flags");
    bool already_has_pic = false;
    for (int i=0;i<flags_metadata->getNumOperands();i++)
    {
      auto flag_operand = flags_metadata->getOperand(i);
      for (int j=0;j<flag_operand->getNumOperands();j++)
      {
        if (auto mdString = dyn_cast<MDString>(flag_operand->getOperand(j))) {
          StringRef str = mdString->getString();
          if (str=="PIC Level") already_has_pic=true;
        }
      }
    }
    if (!already_has_pic) flags_metadata->addOperand(node);
  }

  void fixFunctionAttributes(Function* F)
  {
      F->setDSOLocal(false);
      auto name = F->getName().str();
      if (is_prefix(name,"llvm")) return;
      auto pass =  Attribute::get(F->getContext(),"target-features","+c64,+dotprod,+fp-armv8,+fullfp16,+morello,+neon,+rcpc,+spe,+ssbs,+v8.2a");
      F->addFnAttr(pass);
  }

  bool is_prefix(std::string base, std::string prefix)
  {
    if (prefix.compare(base.substr(0,prefix.length()))==0)
    {
      return true;
    }
    else return false;
  }

  std::vector<std::string> split_string(std::string& s, std::string delimiter) 
  {
    size_t pos_start = 0, pos_end, delim_len = delimiter.length();
    std::string token;
    std::vector<std::string> res;

    while ((pos_end = s.find (delimiter, pos_start)) != std::string::npos) 
    {
        token = s.substr (pos_start, pos_end - pos_start);
        pos_start = pos_end + delim_len;
        res.push_back(token);
    }

    res.push_back (s.substr(pos_start));
    return res;
  }

  bool struct_has_pointer(StructType* struct_type)
  {
    bool has_pointer=false;
    for (auto& elem_type : struct_type->elements())
    {
      if (elem_type->isPointerTy()) 
      {
        has_pointer=true;
        break;
      }
      if (elem_type->isStructTy())
      {
        auto stype2 = dyn_cast<StructType>(elem_type);
        bool elem_has_pointer = struct_has_pointer(stype2);
        if (elem_has_pointer)
        {
          has_pointer=true;
          break;
        }
      }
      if (elem_type->isArrayTy())
      {
        if (array_has_pointer((ArrayType*)elem_type))
        {
          has_pointer = true;
          break;
        }
      }
    }
    has_pointer_map[struct_type]=has_pointer;
    return has_pointer_map[struct_type];
  }

  bool array_has_pointer(ArrayType* array_type)
  {
    bool has_pointer=false;
    if (array_type->getElementType()->isPointerTy()) return true;
    else if (array_type->getElementType()->isStructTy())
    {
      return struct_has_pointer((StructType*)(array_type->getElementType()));
    }
    else if (array_type->getElementType()->isArrayTy())
    {
      return array_has_pointer((ArrayType*)(array_type->getElementType()));
    }
    else return false;
  }

  bool get_alignment_is_higher(Type* var_type)
  {
    if (var_type->isPointerTy()) return true;
    if (var_type->isStructTy())
    {
      if (struct_has_pointer((StructType*)var_type)) return true;
    }
    if (var_type->isArrayTy())
    {
      if (array_has_pointer((ArrayType*)var_type)) return true;
    }
    return false;
  }

  std::unordered_map<GlobalVariable*,GlobalVariable*> globals_that_are_changed_in_constants;

  Constant* changeConstant(Constant* original_constant, Type* struct_type)
  {
    if (old_to_new_variable.find((GlobalVariable*)(original_constant))!=old_to_new_variable.end())
    {
      return old_to_new_variable[(GlobalVariable*)(original_constant)];
    }
    if (original_constant->isNullValue())
    {
      return Constant::getNullValue(struct_type);
    }
    else if (auto const_vector = dyn_cast<ConstantVector>(original_constant))
    {
      std::vector<Constant*> constants;
      for (unsigned i = 0; i<const_vector->getNumOperands();i++)
      {
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(const_vector->getOperand(i)))
        {
          if (CE->getOpcode() == Instruction::IntToPtr)
          {
            auto new_overall_type = changeAddressSpace(CE->getType(),200);
            auto i8_type = Type::getInt8Ty(whole_module->getContext());
            PointerType* i8PtrType = i8_type->getPointerTo(200);
            Constant* null_const = ConstantPointerNull::get(i8PtrType);
            Constant* offset = dyn_cast<ConstantInt>(CE->getOperand(0)); 
            std::vector<Constant*> offsets = {offset}; 
            Constant* get_const = ConstantExpr::getGetElementPtr(i8_type, null_const, offsets);
            Constant* bitcast_constant = ConstantExpr::getBitCast(get_const, new_overall_type);
            constants.push_back(bitcast_constant);
          }
          else if (CE->getOpcode() == Instruction::GetElementPtr || CE->getOpcode() == Instruction::BitCast)
          {
            Constant* my_constant = dyn_cast<Constant>(CE);
            Type* new_constant_type = changeAddressSpace(my_constant->getType(),200);
            constants.push_back(changeConstant(my_constant,new_constant_type));
          }
          else if (CE->getOpcode()==Instruction::PtrToInt)
          {
            // No longer i64, now i8 addrspace(200)*
            Type* new_ty = Type::getInt8Ty(whole_module->getContext())->getPointerTo(200);
            auto first_op = (CE->getOperand(0)); 
            // if it is a constant, we have to change it
            if (isa<Constant>(first_op))
            {
              auto type_const = changeAddressSpace(first_op->getType(),200);
              auto new_const = changeConstant((Constant*)first_op,type_const);
              Constant* bitcast_constant = ConstantExpr::getBitCast(new_const, new_ty);
              constants.push_back(bitcast_constant);
            }
            else // else, we don't
            {
              Constant* bitcast_constant = ConstantExpr::getBitCast(first_op, new_ty);
              constants.push_back(bitcast_constant);
            }
          }
          else constants.push_back(const_vector->getOperand(i)); // Maybe BlockAddress isto?
        }
        else 
        {
          Type* new_type = changeAddressSpace(const_vector->getOperand(i)->getType(),200);
          Constant* const_part = changeConstant(const_vector->getOperand(i),new_type);
          constants.push_back(const_part);
        }
      }
      Constant *constVector = ConstantVector::get(constants);
      return constVector;
    }
    else if (auto const_struct = dyn_cast<ConstantStruct>(original_constant)) 
    {
      std::vector<Constant*> constants;
      for (unsigned i = 0; i<const_struct->getNumOperands();i++)
      {
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(const_struct->getOperand(i)))
        {
          if (CE->getOpcode() == Instruction::IntToPtr)
          {
            auto new_overall_type = changeAddressSpace(CE->getType(),200);
            auto i8_type = Type::getInt8Ty(whole_module->getContext());
            PointerType* i8PtrType = i8_type->getPointerTo(200);
            Constant* null_const = ConstantPointerNull::get(i8PtrType);
            Constant* offset = dyn_cast<ConstantInt>(CE->getOperand(0)); 
            std::vector<Constant*> offsets = {offset}; 
            Constant* get_const = ConstantExpr::getGetElementPtr(i8_type, null_const, offsets);
            Constant* bitcast_constant = ConstantExpr::getBitCast(get_const, new_overall_type);
            constants.push_back(bitcast_constant);
          }
          else if (CE->getOpcode() == Instruction::GetElementPtr || CE->getOpcode() == Instruction::BitCast)
          {
            Constant* my_constant = dyn_cast<Constant>(CE);
            Type* new_constant_type = changeAddressSpace(my_constant->getType(),200);
            constants.push_back(changeConstant(my_constant,new_constant_type));
          }
          else if (CE->getOpcode()==Instruction::PtrToInt)
          {
            // No longer i64, now i8 addrspace(200)*
            Type* new_ty = Type::getInt8Ty(whole_module->getContext())->getPointerTo(200);
            auto first_op = (CE->getOperand(0)); 
            // if it is a constant, we have to change it
            if (isa<Constant>(first_op))
            {
              auto type_const = changeAddressSpace(first_op->getType(),200);
              auto new_const = changeConstant((Constant*)first_op,type_const);
              Constant* bitcast_constant = ConstantExpr::getBitCast(new_const, new_ty);
              constants.push_back(bitcast_constant);
            }
            else // else, we don't
            {
              Constant* bitcast_constant = ConstantExpr::getBitCast(first_op, new_ty);
              constants.push_back(bitcast_constant);
            }
          }
          else constants.push_back(const_struct->getOperand(i)); // Maybe BlockAddress isto?
        }
        else 
        {
          Type* new_type = changeAddressSpace(const_struct->getOperand(i)->getType(),200);
          Constant* const_part = changeConstant(const_struct->getOperand(i),new_type);
          constants.push_back(const_part);
        }
      }
      Constant *constStruct = ConstantStruct::get((StructType*)struct_type, constants);
      return constStruct;
    }
    else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(original_constant))
    {
      if (CE->getOpcode() == Instruction::BitCast)
      {
        Constant* operand = CE->getOperand(0);
        Type* new_operand_type = changeAddressSpace(operand->getType(),200);
        auto new_operand = changeConstant(operand, new_operand_type);
        Type* new_overall_type = changeAddressSpace(CE->getType(),200);
        Constant* bitcast_constant = ConstantExpr::getBitCast(new_operand, new_overall_type);
        return bitcast_constant;
      } 
      else if (CE->getOpcode() == Instruction::IntToPtr)
      {
        auto new_overall_type = changeAddressSpace(CE->getType(),200);
        auto i8_type = Type::getInt8Ty(whole_module->getContext());
        PointerType* i8PtrType = i8_type->getPointerTo(200);
        Constant* null_const = ConstantPointerNull::get(i8PtrType);
        Constant* offset = dyn_cast<ConstantInt>(CE->getOperand(0)); 
        std::vector<Constant*> offsets = {offset}; 
        Constant* get_const = ConstantExpr::getGetElementPtr(i8_type, null_const, offsets);
        Constant* bitcast_constant = ConstantExpr::getBitCast(get_const, new_overall_type);
        return bitcast_constant;
      }
      else if (CE->getOpcode() == Instruction::GetElementPtr)
      {
        Constant* operand = CE->getOperand(0);
        Type* new_operand_type = changeAddressSpace(operand->getType(),200);
        auto new_operand = changeConstant(operand, new_operand_type);
        Type* new_overall_type = changeAddressSpace(CE->getType(),200);
        std::vector<Constant*> idx_vector;
        for (unsigned i = 1; i<CE->getNumOperands();i++)
        {
          idx_vector.push_back(CE->getOperand(i));
        }
        if (auto const_exp = dyn_cast<ConstantExpr>(new_operand))
        {
          if (const_exp->getOpcode() == Instruction::BitCast && const_exp->getType()->isPointerTy() && ((PointerType*)const_exp->getType())->getElementType()->isIntegerTy(8))
          {
            if (const_exp->getOperand(0)->getType()->isPointerTy())
            {
              Type* helper_type = ((PointerType*)(const_exp->getOperand(0)->getType()))->getElementType();
              int without_cheri = get_size(helper_type,false);
              int with_cheri = get_size(helper_type,true);
              if (with_cheri!=without_cheri && idx_vector.size()>0 && isa<ConstantInt>(idx_vector[idx_vector.size()-1]))
              {
                auto const_int = dyn_cast<ConstantInt>(idx_vector[idx_vector.size()-1]);
                auto k = const_int->getValue();
                k*=with_cheri;
                k=k.sdiv(without_cheri);
                ConstantInt* constInt = ConstantInt::get(whole_module->getContext(), k);
                idx_vector[idx_vector.size()-1]=constInt;
              }
            }
          }
        }
        ArrayRef<Constant*> idxList(idx_vector);
        Constant* const_expr = ConstantExpr::getInBoundsGetElementPtr(((PointerType*)new_operand->getType())->getElementType(), new_operand, idxList);
        return const_expr;
      }
      // TODO - probably add other types of opcodes!
      return original_constant;
    }
    else if (auto array_const = dyn_cast<ConstantArray>(original_constant))
    {
      if (array_has_pointer((ArrayType*)(array_const->getType())))
      {
        std::vector<Constant*> constants;
        Type* new_array_type = changeAddressSpace(array_const->getType(),200);
        for (unsigned i = 0, e = array_const->getNumOperands(); i != e; ++i) 
        {
          Constant* elem_const = array_const->getOperand(i);
          Type* new_type = changeAddressSpace(elem_const->getType(),200);
          Constant* new_constant = changeConstant(elem_const,new_type);
          constants.push_back(new_constant);
        }
        ArrayRef<Constant*> arr_const(constants);
        return ConstantArray::get((ArrayType*)new_array_type,arr_const);
      }
      else return original_constant;
    }
    else if (BlockAddress* block_address = dyn_cast<BlockAddress>(original_constant))
    {
      // Make a fake function 
      Function* F = block_address->getFunction();
      if (real_to_fake_functions.find(F)==real_to_fake_functions.end())
      {
        SmallVector<ReturnInst*, 8> Returns;
        auto ft = new_ft_of_function[F];
        auto test_function = Function::Create(ft, F->getLinkage(), 200, "", whole_module);
        test_function->copyAttributesFrom(F);
        Function::arg_iterator DestI = test_function->arg_begin();
        ValueToValueMapTy VMap;
        for (Function::const_arg_iterator J = F->arg_begin(); J != F->arg_end();J++) 
        {
          DestI->setName(J->getName());
          VMap[J] = DestI++;
        }
        auto name = F->getName().str();
        CloneFunctionInto(test_function, F, VMap, CloneFunctionChangeType::GlobalChanges, Returns);
        if (test_function->hasStructRetAttr())
        {
          if (test_function->arg_size()>0 && test_function->getArg(0)->hasStructRetAttr())
          {
            Attribute new_ret_attribute = Attribute::getWithStructRetType(whole_module->getContext(),test_function->getArg(0)->getType());
            test_function->getArg(0)->removeAttr(Attribute::StructRet);
            test_function->getArg(0)->addAttr(new_ret_attribute);
          }
          if (test_function->arg_size()>1 && test_function->getArg(1)->hasStructRetAttr())
          {
            Attribute new_ret_attribute = Attribute::getWithStructRetType(whole_module->getContext(),test_function->getArg(1)->getType());
            test_function->getArg(1)->removeAttr(Attribute::StructRet);
            test_function->getArg(1)->addAttr(new_ret_attribute);
          }
        }
        real_to_fake_functions[F]=test_function;
        fake_to_real_functions[test_function]=F;
        // Do basic block mapping
        std::vector<BasicBlock*> old_bbs;
        for (BasicBlock& bb : *F)
        {
          old_bbs.push_back(&bb);
        }
        int cnt=0;
        for (BasicBlock& new_bb : *test_function)
        {
          BasicBlock* old_bb = old_bbs[cnt];
          real_to_fake_basicBlocks[old_bb]=&new_bb;
          fake_to_real_basicBlocks[&new_bb]=old_bb;
          cnt++;
        }
        auto fun_name = F->getName().str();
        F->setName("");
        test_function->setName(fun_name);
        functions_to_fix_later.insert(F);
      }
      Function* fake_fun = real_to_fake_functions[F];
      BasicBlock* fake_bb = real_to_fake_basicBlocks[block_address->getBasicBlock()];
      BlockAddress* return_block_address = BlockAddress::get(fake_fun, fake_bb);
      return return_block_address;
    }
    else if (auto const_inner_function = dyn_cast<Function>(original_constant))
    {
      // Make a fake function 
      Function* F = const_inner_function;
      if (real_to_fake_functions.find(F)==real_to_fake_functions.end())
      {
        SmallVector<ReturnInst*, 8> Returns;
        auto ft = new_ft_of_function[F];
        auto name = F->getName().str();
        F->setName("");
        auto test_function = Function::Create(ft, F->getLinkage(), 200, name, whole_module);
        test_function->copyAttributesFrom(F);
        Function::arg_iterator DestI = test_function->arg_begin();
        ValueToValueMapTy VMap;
        for (Function::const_arg_iterator J = F->arg_begin(); J != F->arg_end();J++) 
        {
          DestI->setName(J->getName());
          VMap[J] = DestI++;
        }
        CloneFunctionInto(test_function, F, VMap, CloneFunctionChangeType::GlobalChanges, Returns);
        if (test_function->hasStructRetAttr())
        {
          if (test_function->arg_size()>0 && test_function->getArg(0)->hasStructRetAttr())
          {
            Attribute new_ret_attribute = Attribute::getWithStructRetType(whole_module->getContext(),test_function->getArg(0)->getType());
            test_function->getArg(0)->removeAttr(Attribute::StructRet);
            test_function->getArg(0)->addAttr(new_ret_attribute);
          }
          if (test_function->arg_size()>1 && test_function->getArg(1)->hasStructRetAttr())
          {
            Attribute new_ret_attribute = Attribute::getWithStructRetType(whole_module->getContext(),test_function->getArg(1)->getType());
            test_function->getArg(1)->removeAttr(Attribute::StructRet);
            test_function->getArg(1)->addAttr(new_ret_attribute);
          }
        }
        real_to_fake_functions[F]=test_function;
        fake_to_real_functions[test_function]=F;
        // Do basic block mapping
        std::vector<BasicBlock*> old_bbs;
        for (BasicBlock& bb : *F)
        {
          old_bbs.push_back(&bb);
        }
        int cnt=0;
        for (BasicBlock& new_bb : *test_function)
        {
          BasicBlock* old_bb = old_bbs[cnt];
          real_to_fake_basicBlocks[old_bb]=&new_bb;
          fake_to_real_basicBlocks[&new_bb]=old_bb;
          cnt++;
        }
        functions_to_fix_later.insert(F);
      }
      Function* fake_fun = real_to_fake_functions[F];
      return (Constant*)fake_fun;
    }
    else if (ConstantPointerNull* null_pointer = dyn_cast<ConstantPointerNull>(original_constant))
    {
      auto new_type = changeAddressSpace(original_constant->getType(),200);
      return ConstantPointerNull::get((PointerType*)new_type);
    }
    else if (GlobalVariable* global = dyn_cast<GlobalVariable>(original_constant))
    {
      auto changed_global = changeGlobalVariable(global);
      if (globals_that_are_changed_in_constants.find(global)==globals_that_are_changed_in_constants.end())
      {
        globals_that_are_changed_in_constants[global]=changed_global;
      }
      return changed_global;
    }
    else return original_constant;
  }

  void change_all_aliases(Constant* old_gv, Constant* new_gv)
  {
    if (map_const_to_alias.find(old_gv)!=map_const_to_alias.end())
    {
      auto& aliases = map_const_to_alias[old_gv];
      for (auto& alias : aliases)
      {
        alias->mutateType(new_gv->getType());
        alias->setAliasee(new_gv);
        alias->setDSOLocal(false);
      }
    }
  }

  GlobalVariable* changeGlobalVariable(GlobalVariable* global)
  {
    auto type = global->getType();
    auto var_name = global->getName();
    if (already_changed_global_variables.find(global)!=already_changed_global_variables.end()) return global;
    if (type->isPointerTy())
    {
      if (global->getLinkage()==GlobalValue::LinkageTypes::ExternalLinkage) global->setDSOLocal(false);
      auto point = changeAddressSpace(type,200);
      auto name_global = global->getName().str();
      // Does not have initializer
      if (!global->hasInitializer())
      {
        global->setName("");
        GlobalVariable* test_gv = new GlobalVariable(*global->getParent(), ((PointerType*)point)->getElementType(), global->isConstant(), global->getLinkage(), nullptr, name_global, global, global->getThreadLocalMode(), 200);
        //global->mutateType(point);
        test_gv->copyAttributesFrom(global);
        old_to_new_variable[global]=test_gv;
        if (get_alignment_is_higher(((PointerType*)point)->getElementType()))
        {
          test_gv->setAlignment(Align(16));
        }
        ReplaceUnsafe(global,test_gv);
        already_changed_global_variables.insert(test_gv);
        return test_gv;
      }
      if (((PointerType*)type)->getElementType()->isPointerTy())
      {
        global->setName("");
        auto new_type = changeAddressSpace(((PointerType*)type)->getElementType(),200);
        auto new_constant = changeConstant(global->getInitializer(), new_type);
        GlobalVariable* test_gv = new GlobalVariable(*global->getParent(), ((PointerType*)point)->getElementType(), global->isConstant(), global->getLinkage(), new_constant, name_global, global, global->getThreadLocalMode(), 200);
        test_gv->copyAttributesFrom(global);
        old_to_new_variable[global]=test_gv;
        if (get_alignment_is_higher(((PointerType*)point)->getElementType()))
        {
          test_gv->setAlignment(Align(16));
        }
        ReplaceUnsafe(global,test_gv);
        already_changed_global_variables.insert(test_gv);
        return test_gv;
      }
      else if (((PointerType*)type)->getElementType()->isStructTy())
      {
        auto new_type = changeAddressSpace(((PointerType*)type)->getElementType(),200);
        auto old_type = ((PointerType*)type)->getElementType();
        if (!has_pointer_map[(StructType*)old_type]) 
        {
          global->setName("");
          GlobalVariable* test_gv = new GlobalVariable(*global->getParent(), new_type, global->isConstant(), global->getLinkage(), global->getInitializer(), name_global, global, global->getThreadLocalMode(), 200);
          test_gv->copyAttributesFrom(global);
          old_to_new_variable[global]=test_gv;
          if (get_alignment_is_higher(((PointerType*)point)->getElementType()))
          {
            test_gv->setAlignment(Align(16));
          }
          already_changed_global_variables.insert(test_gv);
          return test_gv;
        }
        else
        {
          auto new_type = changeAddressSpace(((PointerType*)type)->getElementType(),200);
          Constant *constStruct = changeConstant(global->getInitializer(), new_type);
          global->setName("");
          GlobalVariable* test_gv = new GlobalVariable(*global->getParent(), new_type, global->isConstant(), global->getLinkage(), constStruct, name_global, global, global->getThreadLocalMode(), 200);
          test_gv->copyAttributesFrom(global);
          old_to_new_variable[global]=test_gv;
          if (get_alignment_is_higher(((PointerType*)point)->getElementType()))
          {
            test_gv->setAlignment(Align(16));
          }
          already_changed_global_variables.insert(test_gv);
          return test_gv;
        }
      }
      else if (((PointerType*)type)->getElementType()->isArrayTy())
      {
        auto new_type = changeAddressSpace(((PointerType*)type)->getElementType(),200);
        Constant *constStruct = changeConstant(global->getInitializer(), new_type);
        global->setName("");
        GlobalVariable* test_gv = new GlobalVariable(*global->getParent(), new_type, global->isConstant(), global->getLinkage(), constStruct, name_global, global, global->getThreadLocalMode(), 200);
        test_gv->copyAttributesFrom(global);

        old_to_new_variable[global]=test_gv;
        if (get_alignment_is_higher(((PointerType*)point)->getElementType()))
        {
          test_gv->setAlignment(Align(16));
        }
        already_changed_global_variables.insert(test_gv);
        return test_gv;
      }
      else 
      {
        if (get_alignment_is_higher(((PointerType*)point)->getElementType()))
        {
          global->setAlignment(Align(16));
        }
        global->mutateType(point);
        already_changed_global_variables.insert(global);
        return global;
      }
    }
    already_changed_global_variables.insert(global);
    return global;
  }

  void fixCallFunctions(Module& M)
  {
    // For regular calls
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {      
          // Fix call functions
          if (auto call_inst = dyn_cast<CallInst>(&I)) 
          {
            if (call_inst->getCalledFunction()) // Direct call
            {
              auto func_type = call_inst->getCalledFunction()->getFunctionType();
              call_inst->mutateFunctionType(func_type);
            }
            else // Indirect call
            {
              auto func = call_inst->getCalledOperand();
              FunctionType* func_type = dyn_cast<FunctionType>(func->getType()->getPointerElementType());
              call_inst->mutateFunctionType(func_type);
            }
          }
        }
      }
    }

    // Now for srets
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {      
          // Fix call functions
          if (auto call_inst = dyn_cast<CallInst>(&I)) 
          {
            if (call_inst->arg_size()>0)
            {
              if (call_inst->paramHasAttr(0,Attribute::StructRet))
              {
                call_inst->removeParamAttr(0,Attribute::StructRet);
                Attribute new_ret_attribute = Attribute::getWithStructRetType(M.getContext(),call_inst->getArgOperand(0)->getType());
                call_inst->addParamAttr(0,new_ret_attribute);
              }
            }
            if (call_inst->arg_size()>1)
            {
              if (call_inst->paramHasAttr(1,Attribute::StructRet))
              {
                call_inst->removeParamAttr(1,Attribute::StructRet);
                Attribute new_ret_attribute = Attribute::getWithStructRetType(M.getContext(),call_inst->getArgOperand(1)->getType());
                call_inst->addParamAttr(1,new_ret_attribute);
              }
            }
          }
        }
      }
    }
  }


  bool runOnModule(Module& M)
  {
    whole_module=&M;
    StringRef data_layout = "e-m:e-pf200:128:128:128:64-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-A200-P200-G200";
    M.setDataLayout(data_layout);
    std::vector<Function*> old_functions;
    std::vector<Function*> new_functions;
    // Functions (just types mostly)
    for (auto& F : M)
    {
      old_functions.push_back(&F);
    }
    add_module_flags(M);
    for (auto& F : old_functions)
    {
      fixFunctionAttributes(F);
    }
    std::vector<FunctionType*> fts;
    for (auto& F : old_functions)
    {
      std::vector<Argument*> arguments_pointer;
      std::vector<Type*> new_types;
      for (Function::const_arg_iterator J = F->arg_begin(); J != F->arg_end();J++) 
      {
        Argument* a = (Argument*)&(*J);
        arguments_pointer.push_back(a);
      }
      int cnt=0;
      for (auto& J : arguments_pointer)
      {
        auto old_type = J->getType();
        bool is_va_list=false;
        // Check if it is va_list
        if (isa<PointerType>(old_type))
        {
          auto point_type = dyn_cast<PointerType>(old_type);
          if (check_if_pointer_type_to_va_list(point_type))
          {
            changed_functions_for_vararg.insert(F);
            Type* new_va_type = change_from_va_type(old_type);
            new_types.push_back(new_va_type);
            is_va_list=true; 
            old_changed_for_va_arguments[F].insert(cnt);
          }
        }
        if (!is_va_list) 
        {
          auto new_type = changeAddressSpace(J->getType(), 200);
          new_types.push_back(new_type);
        }
        cnt++;
      }
      ArrayRef<Type*> ar(new_types);
      auto new_type = changeAddressSpace(F->getReturnType(),200);
      FunctionType* ft = FunctionType::get(new_type, ar, F->getFunctionType()->isVarArg());
      fts.push_back(ft);
      new_ft_of_function[F]=ft;
    }
    std::unordered_set<Constant*> already_done;
    // Globals
    std::vector<GlobalVariable*> globals;
    for (auto& global : M.getGlobalList())
    {
      globals.push_back(&global);
    }
    // Fix constants in instructions - only for PHI nodes!
    while (true)
    {
      bool has_constexp = false;
      for (auto& F : M)
      {
        for (auto& B : F)
        {
          for (auto& I : B)
          {
            auto instruction_name = I.getOpcodeName();
            bool has_operands = false;
            for (int i = 0; i < I.getNumOperands(); i++) 
            {
              auto operand_of = I.getOperand(i);
              if (isa<Constant>(operand_of) && already_done.find((Constant*)operand_of)==already_done.end())
              {
                if (isa<ConstantAggregate>(operand_of))
                {
                  auto changed_type = changeAddressSpace(operand_of->getType(),200);
                  auto changed_constant = changeConstant((Constant*)operand_of,changed_type);
                  already_done.insert(changed_constant);
                  I.setOperand(i,changed_constant);
                }
              }
              if (isa<ConstantExpr>(operand_of)) 
              {
                if (isa<PHINode>(&I) && already_done.find((Constant*)operand_of)==already_done.end())
                {
                  auto changed_type = changeAddressSpace(operand_of->getType(),200);
                  auto changed_constant = changeConstant((Constant*)operand_of,changed_type);
                  already_done.insert(changed_constant);
                  I.setOperand(i,changed_constant);
                }
                else if (!isa<PHINode>(&I))
                {
                  Instruction* helper;
                  ConstantExpr* const_expr = dyn_cast<ConstantExpr>(operand_of);
                  helper = const_expr->getAsInstruction();
                  helper->setName(I.getName().str()+".helper");
                  helper->insertBefore(&I);
                  I.setOperand(i, helper);
                  has_constexp = true;
                }
              }
            }
          }
        }
      }
      if (!has_constexp) break;
    }
    for (auto& ali : M.aliases())
    {
      ali.setDSOLocal(false);
      map_const_to_alias[ali.getAliasee()].push_back(&ali);
    }
    for (auto& global : globals)
    {
      changeGlobalVariable(global);
    }
    for (auto& pair : globals_that_are_changed_in_constants)
    {
      auto old_global = pair.first;
      auto new_global = pair.second;
      if (old_global!=new_global)
      {
        ReplaceUnsafe(old_global,new_global);
      }
    }
    // Fix all aliases (or only those who are in a map)
    for (auto& old_to_new : old_to_new_variable)
    {
      auto old_const = dyn_cast<Constant>(old_to_new.first);
      auto new_const = dyn_cast<Constant>(old_to_new.second);
      if (old_const && new_const)
      {
        change_all_aliases(old_const, new_const);
      }
    }
    // Struct Types
    std::vector<StructType*> struct_types;
    for (auto& sType : M.getIdentifiedStructTypes())
    {
      struct_types.push_back(sType);
    }
    for (auto& sType : struct_types)
    {
      std::vector<Type*> types;
      bool has_pointer=false;
      for (auto& elem_type : sType->elements())
      {
        if (elem_type->isPointerTy()) has_pointer=true;
      }
    }
    std::vector<AllocaInst*> instructions_alloca;
    std::vector<Value*> ins_with_pointers;

    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          auto instruction_name = I.getOpcodeName();
          // If it is a load instruction, we need to change the type
          if (auto load_inst = dyn_cast<LoadInst>(&I))
          {
            auto old_type = I.getType();
            auto newType = changeAddressSpace(old_type,200);
            I.mutateType(newType);
          }
          // Same if its a GEP
          if (auto gep_inst = dyn_cast<GetElementPtrInst>(&I))
          {
            auto old_type = I.getType();
            auto newType = changeAddressSpace(old_type,200);
            I.mutateType(newType);
          }
          for (int i = 0; i < I.getNumOperands(); i++) 
          {
            auto operand_of = I.getOperand(i);
            GlobalVariable *GV = dyn_cast<GlobalVariable>(operand_of);
            if (GV && old_to_new_variable.find(GV)!=old_to_new_variable.end())
            {
              I.setOperand(i, old_to_new_variable[GV]);
            }
            else if (operand_of->getType()->isPointerTy() || operand_of->getType()->isStructTy())
            {
              auto new_type = (changeAddressSpace(operand_of->getType(), 200));
              operand_of->mutateType(new_type);
              I.setOperand(i, operand_of);
            }
          }
        }
      }
    }
    int cnt=0;

    for (auto& F : old_functions)
    {
      if (real_to_fake_functions.find(F)==real_to_fake_functions.end())
      {
        SmallVector<ReturnInst*, 8> Returns;
        auto ft = fts[cnt];
        auto test_function = Function::Create(ft, F->getLinkage(), 200, "", &M);
        test_function->copyAttributesFrom(F);
        Function::arg_iterator DestI = test_function->arg_begin();
        ValueToValueMapTy VMap;
        for (Function::const_arg_iterator J = F->arg_begin(); J != F->arg_end();J++) 
        {
          DestI->setName(J->getName());
          VMap[J] = DestI++;
        }
        auto name = F->getName().str();
        CloneFunctionInto(test_function, F, VMap, CloneFunctionChangeType::GlobalChanges, Returns);
        if (test_function->hasStructRetAttr())
        {
          if (test_function->arg_size()>0 && test_function->getArg(0)->hasStructRetAttr())
          {
            Attribute new_ret_attribute = Attribute::getWithStructRetType(M.getContext(),test_function->getArg(0)->getType());
            test_function->getArg(0)->removeAttr(Attribute::StructRet);
            test_function->getArg(0)->addAttr(new_ret_attribute);
          }
          if (test_function->arg_size()>1 && test_function->getArg(1)->hasStructRetAttr())
          {
            Attribute new_ret_attribute = Attribute::getWithStructRetType(M.getContext(),test_function->getArg(1)->getType());
            test_function->getArg(1)->removeAttr(Attribute::StructRet);
            test_function->getArg(1)->addAttr(new_ret_attribute);
          }
        }
        real_to_fake_functions[F]=test_function;
        fake_to_real_functions[test_function]=F;
        // Do basic block mapping
        std::vector<BasicBlock*> old_bbs;
        for (BasicBlock& bb : *F)
        {
          old_bbs.push_back(&bb);
        }
        int cnt=0;
        for (BasicBlock& new_bb : *test_function)
        {
          BasicBlock* old_bb = old_bbs[cnt];
          real_to_fake_basicBlocks[old_bb]=&new_bb;
          fake_to_real_basicBlocks[&new_bb]=old_bb;
          cnt++;
        }
        ReplaceUnsafe(F,test_function);
        F->setName("");
        F->eraseFromParent();
        test_function->setName(name);
      }
      Function* test_function=real_to_fake_functions[F];
      auto name = test_function->getName().str();
      // Change name if it is intristic llvm function
      if (is_prefix(name,"llvm"))
      {
        auto splitted_name = split_string(name,".");
        std::string new_name="";
        for (auto& separate : splitted_name)
        {
          if (is_prefix(separate,"p0"))
          {
            auto pos = separate.find('i');
            if (pos==std::string::npos) continue;
            std::string new_name_help = "p200";
            new_name_help = new_name_help + separate.substr(pos);
            new_name = new_name+new_name_help+".";
          }
          else new_name = new_name+separate+".";
        }
        new_name = new_name.substr(0,new_name.length()-1);
        name = new_name;
        test_function->setName(name);
      }
      for (auto& B : *test_function)
      {
        for (auto& I : B)
        {
          auto instruction_name = I.getOpcodeName();
          for (int i = 0; i < I.getNumOperands(); i++) 
          {
            auto operand_of = I.getOperand(i);
            auto new_type = (changeAddressSpace(operand_of->getType(), 200));
            operand_of->mutateType(new_type);
            I.setOperand(i, operand_of);
          }
          if (auto alloca_inst = dyn_cast<AllocaInst>(&I))
          {
            auto type_alloca = alloca_inst->getAllocatedType();
            auto new_type = (changeAddressSpace(type_alloca, 200));
            alloca_inst->setAllocatedType(new_type);
            type_alloca = alloca_inst->getAllocatedType();
            if (alloca_inst->getAllocatedType()->isPointerTy())
            {
              alloca_inst->setAlignment(Align(16));
            }
            else
            {
              if (type_alloca->isStructTy())
              {
                auto ST = dyn_cast<StructType>(type_alloca);
                if (struct_has_pointer(ST))
                {
                  alloca_inst->setAlignment(Align(16));
                }
              }
              if (type_alloca->isArrayTy())
              {
                if (array_has_pointer((ArrayType*)type_alloca))
                {
                  alloca_inst->setAlignment(Align(16));
                }
              }
            }
          }
          // Change allignments
          if (auto store_inst = dyn_cast<StoreInst>(&I)) 
          {
            if (store_inst->getOperand(0)->getType()->isPointerTy())
            {
              store_inst->setAlignment(Align(16));
            }
            else
            {
              auto op_inst = dyn_cast<Instruction>(store_inst->getOperand(1));
              if (op_inst)
              {
                if (auto getelemptr_inst = dyn_cast<GetElementPtrInst>(op_inst))
                {
                  auto elem_type = getelemptr_inst->getSourceElementType();
                  ConstantInt* con_int = nullptr;
                  bool are_all_constant = true;
                  // Check if all the indices are constant
                  for (auto& k : getelemptr_inst->indices())
                  {
                    if (isa<ConstantInt>(k))
                    {
                      con_int=dyn_cast<ConstantInt>(k);
                    }
                    else
                    {
                      are_all_constant=false;
                    }
                  }
                  if (are_all_constant && con_int->isZero()) /// This needs to be changed!
                  {
                    if (elem_type->isStructTy())
                    {
                      auto ST = dyn_cast<StructType>(elem_type);
                      if (has_pointer_map.find(ST)!=has_pointer_map.end() && has_pointer_map[ST])
                      {
                        store_inst->setAlignment(Align(16));
                      }
                    }
                    else if (elem_type->isArrayTy())
                    {
                      if (array_has_pointer((ArrayType*)elem_type))
                      {
                        store_inst->setAlignment(Align(16));
                      }
                    }
                  }
                  else if (are_all_constant)
                  {
                    if (elem_type->isStructTy())
                    {
                      int val = con_int->getZExtValue(); 
                      if (does_field_need_alignment((StructType*)elem_type,val))
                      {
                        store_inst->setAlignment(Align(16));
                      }
                    }
                  }
                }
              }
            }
          }
          if (auto load_inst = dyn_cast<LoadInst>(&I)) 
          {
            if (load_inst->getType()->isPointerTy())
            {
              load_inst->setAlignment(Align(16));
            }
            else 
            {
              auto op_inst = dyn_cast<Instruction>(load_inst->getOperand(0));
              if (op_inst)
              {
                if (auto getelemptr_inst = dyn_cast<GetElementPtrInst>(op_inst))
                {
                  auto elem_type = getelemptr_inst->getSourceElementType();
                  ConstantInt* con_int = nullptr;
                  bool are_all_constant = true;
                  // Check if all the indices are constant
                  for (auto& k : getelemptr_inst->indices())
                  {
                    if (isa<ConstantInt>(k))
                    {
                      con_int=dyn_cast<ConstantInt>(k);
                    }
                    else
                    {
                      are_all_constant=false;
                    }
                  }
                  if (are_all_constant && con_int->isZero()) // We can change only if we know all are constant, otherwise, who knows
                  {
                    if (elem_type->isStructTy())
                    {
                      auto ST = dyn_cast<StructType>(elem_type);
                      if (struct_has_pointer(ST))
                      {
                        load_inst->setAlignment(Align(16));
                      }
                    }
                    else if (elem_type->isArrayTy())
                    {
                      if (array_has_pointer((ArrayType*)elem_type))
                      {
                        load_inst->setAlignment(Align(16));
                      }
                    }
                  }
                  else if (are_all_constant)
                  {
                    if (elem_type->isStructTy())
                    {
                      int val = con_int->getZExtValue(); 
                      if (does_field_need_alignment((StructType*)elem_type,val))
                      {
                        load_inst->setAlignment(Align(16));
                      }
                    }
                  }
                }
                else if (auto bitcast_inst = dyn_cast<BitCastInst>(op_inst))
                {
                  if (bitcast_inst->getOperand(0)->getType()->isPointerTy())
                  {
                    PointerType* pointer_type = (PointerType*)bitcast_inst->getOperand(0)->getType();
                    if (auto ST = dyn_cast<StructType>(pointer_type->getElementType()))
                    {
                      if (struct_has_pointer(ST))
                      {
                        load_inst->setAlignment(Align(16));
                      }
                    }
                  }
                }
              }
            }
          }
          // Change getelementPr instructions
          if (auto getelemptr_inst = dyn_cast<GetElementPtrInst>(&I)) 
          {
            auto old_type = getelemptr_inst->getSourceElementType();
            auto new_type = changeAddressSpace(old_type, 200);
            getelemptr_inst->setSourceElementType(new_type);
            // Find new resultElement type
            std::vector<Value*> idx_vector;
            for (auto it = getelemptr_inst->idx_begin(); it != getelemptr_inst->idx_end(); it++) 
            {
              idx_vector.push_back(*it);
            }
            ArrayRef<Value*> idxList(idx_vector);
            auto new_res_type = GetElementPtrInst::getIndexedType(new_type, idxList); // This may be subsituted with other, getReturnedType function
            getelemptr_inst->setResultElementType(new_res_type);
          }
        }
      }
      cnt++;
    }

    // Fix call functions - first time
    fixCallFunctions(M);

    // Fix ptrtoint in all the functions
    std::unordered_map<Instruction*, Instruction*> changed_insts;
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {      
          Instruction* inst = &I;
          // Fix PtrToInt
          if (inst->getOpcode() == Instruction::PtrToInt && inst->getType()==Type::getInt64Ty(M.getContext()))
          {
            //Function* f = dyn_cast<Function>(fun.getCallee());
            auto i8_type = Type::getInt8Ty(M.getContext());
            PointerType* i8PtrType = i8_type->getPointerTo(200);
            auto value = inst->getOperand(0);
            auto id = Function::lookupIntrinsicID("llvm.cheri.cap.address.get.i64");
            auto i64_type = Type::getInt64Ty(M.getContext());
            std::vector<Type*> over_types;
            over_types.push_back(i64_type);
            std::vector<Value*> arguments;
            if (value->getType()!=i8PtrType)
            {
              auto first_inst = new BitCastInst(value,i8PtrType,"",inst);
              arguments.push_back(first_inst);
            }
            else
            {
              arguments.push_back(value);
            }
            auto instrisic_function = Intrinsic::getDeclaration(&M,id,ArrayRef<Type*>(over_types));
            auto name = inst->getName().str();
            ArrayRef<Value*> args(arguments);
            CallInst* call_inst = CallInst::Create(instrisic_function->getFunctionType(),instrisic_function,args,name,inst);
            changed_insts[call_inst]=inst;
          }
          // Fix intToPtr
          if (inst->getOpcode() == Instruction::IntToPtr && inst->getOperand(0)->getType()==Type::getInt64Ty(M.getContext()))
          {
            PointerType* pt = (PointerType*)inst->getType();
            ConstantPointerNull *NullPtr = ConstantPointerNull::get(pt);
            std::vector<Value *> GepIndices;
            GepIndices.push_back(inst->getOperand(0));
            GetElementPtrInst* gep_inst = GetElementPtrInst::Create(pt->getElementType(), NullPtr, GepIndices, "",inst);
            changed_insts[gep_inst]=inst;
          }
        }
      }
    }
    // Alignments for some memcpy and memset are not changed by default, change them manually
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {     
          if (auto call_inst = dyn_cast<CallInst>(&I))
          {
            bool changed=false;
            Function* f = call_inst->getCalledFunction();
            std::string name = "";
            if (f) name = f->getName().str();
            // Do this only if it is not memcpy or similar
            if (!(is_prefix(name,"llvm.memcpy") || is_prefix(name,"llvm.memset")))
            {
              for (int i=0;i<call_inst->getNumArgOperands();i++)
              {
                if (call_inst->getArgOperand(i)->getType()->isPointerTy() || call_inst->getOperand(i)->getType()->isArrayTy())
                {
                  if (call_inst->getParamAlign(i).valueOrOne().value()==8)
                  {
                    AttributeList attrList = call_inst->getAttributes();
                    AttributeList newAttrList = attrList.removeAttribute(
                                                call_inst->getContext(),
                                                i+1, 
                                                Attribute::Alignment);
                    newAttrList = newAttrList.addAttribute(
                        call_inst->getContext(),
                        i+1, // the index of the parameter to modify (1-based)
                        Attribute::getWithAlignment(call_inst->getContext(), Align(16)));  
                    call_inst->setAttributes(newAttrList);
                    changed=true;
                  }
                }
              }  
            }
            else // if it is memcpy or memset!
            {
              for (int i=0;i<call_inst->getNumArgOperands();i++)
              {
                if (call_inst->getArgOperand(i)->getType()->isPointerTy())
                {
                  PointerType* point_type = (PointerType*)(call_inst->getArgOperand(i)->getType()); 
                  Instruction* op_inst = dyn_cast<Instruction>(call_inst->getArgOperand(i));
                  if (op_inst)
                  {
                    if (auto getelemptr_inst = dyn_cast<GetElementPtrInst>(op_inst))
                    {
                      auto elem_type = getelemptr_inst->getSourceElementType();
                      ConstantInt* con_int = nullptr;
                      bool are_all_constant = true;
                      // Check if all the indices are constant
                      for (auto& k : getelemptr_inst->indices())
                      {
                        if (isa<ConstantInt>(k))
                        {
                          con_int=dyn_cast<ConstantInt>(k);
                        }
                        else
                        {
                          are_all_constant=false;
                        }
                      }
                      if (are_all_constant && con_int->isZero()) // We can change only if we know all are constant, otherwise, who knows
                      {
                        if (elem_type->isStructTy())
                        {
                          auto ST = dyn_cast<StructType>(elem_type);
                          if (struct_has_pointer(ST))
                          {
                            if (call_inst->getParamAlign(i).valueOrOne().value()==8)
                            {
                              AttributeList attrList = call_inst->getAttributes();
                              AttributeList newAttrList = attrList.removeAttribute(
                                                          call_inst->getContext(),
                                                          i+1, 
                                                          Attribute::Alignment);
                              newAttrList = newAttrList.addAttribute(
                                  call_inst->getContext(),
                                  i+1, // the index of the parameter to modify (1-based)
                                  Attribute::getWithAlignment(call_inst->getContext(), Align(16)));  
                              call_inst->setAttributes(newAttrList);
                            }
                          }
                        }
                        else if (elem_type->isArrayTy())
                        {
                          auto AT = dyn_cast<ArrayType>(elem_type);
                          if (array_has_pointer(AT))
                          {
                            if (call_inst->getParamAlign(i).valueOrOne().value()==8)
                            {
                              AttributeList attrList = call_inst->getAttributes();
                              AttributeList newAttrList = attrList.removeAttribute(
                                                          call_inst->getContext(),
                                                          i+1, 
                                                          Attribute::Alignment);
                              newAttrList = newAttrList.addAttribute(
                                  call_inst->getContext(),
                                  i+1, // the index of the parameter to modify (1-based)
                                  Attribute::getWithAlignment(call_inst->getContext(), Align(16)));  
                              call_inst->setAttributes(newAttrList);
                            }
                          }
                        }
                      }
                    }
                    else if (auto bitcast_inst = dyn_cast<BitCastInst>(op_inst))
                    {
                      if (bitcast_inst->getOperand(0)->getType()->isPointerTy())
                      {
                        PointerType* pointer_type = (PointerType*)bitcast_inst->getOperand(0)->getType();
                        if (auto ST = dyn_cast<StructType>(pointer_type->getElementType()))
                        {
                          if (struct_has_pointer(ST))
                          {
                            if (call_inst->getParamAlign(i).valueOrOne().value()==8)
                            {
                              AttributeList attrList = call_inst->getAttributes();
                              AttributeList newAttrList = attrList.removeAttribute(
                                                          call_inst->getContext(),
                                                          i+1, 
                                                          Attribute::Alignment);
                              newAttrList = newAttrList.addAttribute(
                                  call_inst->getContext(),
                                  i+1, // the index of the parameter to modify (1-based)
                                  Attribute::getWithAlignment(call_inst->getContext(), Align(16)));  
                              call_inst->setAttributes(newAttrList);
                            }
                          }
                        }
                        if (auto AT = dyn_cast<ArrayType>(pointer_type->getElementType()))
                        {
                          if (array_has_pointer(AT))
                          {
                            if (call_inst->getParamAlign(i).valueOrOne().value()==8)
                            {
                              AttributeList attrList = call_inst->getAttributes();
                              AttributeList newAttrList = attrList.removeAttribute(
                                                          call_inst->getContext(),
                                                          i+1, 
                                                          Attribute::Alignment);
                              newAttrList = newAttrList.addAttribute(
                                  call_inst->getContext(),
                                  i+1, // the index of the parameter to modify (1-based)
                                  Attribute::getWithAlignment(call_inst->getContext(), Align(16)));  
                              call_inst->setAttributes(newAttrList);
                            }
                          }
                        }
                      }
                    }
                  }
                  if (get_alignment_is_higher(point_type->getElementType()))
                  {
                    AttributeList attrList = call_inst->getAttributes();
                    AttributeList newAttrList = attrList.removeAttribute(
                                                call_inst->getContext(),
                                                i+1, 
                                                Attribute::Alignment);
                    newAttrList = newAttrList.addAttribute(
                        call_inst->getContext(),
                        i+1, // the index of the parameter to modify (1-based)
                        Attribute::getWithAlignment(call_inst->getContext(), Align(16)));  
                    call_inst->setAttributes(newAttrList);
                    changed=true;
                  }
                }
              }  
            } 
            // if it is memcpy, or memset, and we point to a pointer, it needs to be change the size
            if (!f) continue; // for asm calls
            if ((is_prefix(name,"llvm.memcpy") || is_prefix(name,"llvm.memset")) && call_inst->getArgOperand(0)->getType()->isPointerTy())
            {
              Instruction* op_inst = dyn_cast<Instruction>(call_inst->getArgOperand(0));
              if (op_inst && op_inst->getOpcode() == Instruction::BitCast)
              {
                auto op0 = op_inst->getOperand(0);
                auto point_type = ((PointerType*)op0->getType())->getElementType();
                int with_cheri = get_size(point_type, true);
                int without_cheri = get_size(point_type, false);
                if (with_cheri!=without_cheri) // if the sizes are different
                {
                  auto val = call_inst->getArgOperand(2);
                  bool do_anything = true;
                  // If it is already an add which simbolizes sizeof(), do not to anything
                  if (auto ins = dyn_cast<Instruction>(val))
                  {
                    if (ins->getOpcode() == Instruction::Add)
                    {
                      if (auto md = ins->getMetadata("sizeof"))
                      {
                        do_anything = false;
                      }
                    }
                  }
                  if (do_anything)
                  {
                    AllocaInst* allocaInst = new AllocaInst(val->getType(), 200, "", call_inst);
                    StoreInst* storeInst = new StoreInst(val, allocaInst, false, call_inst);
                    LoadInst *load = new LoadInst(val->getType(), allocaInst, "", call_inst);
                    Constant *c = ConstantInt::get(val->getType(), without_cheri);
                    Value *result = BinaryOperator::CreateSDiv(load, c, "", call_inst);
                    StoreInst *storeInst2 = new StoreInst(result, allocaInst, call_inst);
                    Constant *c2 = ConstantInt::get(val->getType(), with_cheri);
                    LoadInst *load2 = new LoadInst(val->getType(), allocaInst, "", call_inst);
                    Value *result2 = BinaryOperator::CreateMul(load2, c2, "", call_inst);
                    StoreInst *storeInst3 = new StoreInst(result2, allocaInst, call_inst);
                    LoadInst *load3 = new LoadInst(val->getType(), allocaInst, "", call_inst);
                    call_inst->setArgOperand(2,load3);
                    if (call_inst->getDereferenceableBytes(1)>0)
                    {
                      uint64_t derefer = call_inst->getDereferenceableBytes(1);
                      derefer*=with_cheri;
                      derefer/=without_cheri;
                      ConstantInt* const_int = ConstantInt::get(M.getContext(), APInt(64, call_inst->getDereferenceableBytes(1)));  
                      storeInst->setOperand(0,const_int);
                      AttributeList attrList = call_inst->getAttributes();
                      AttributeList newAttrList = attrList.removeAttribute(
                                                  call_inst->getContext(),
                                                  1, 
                                                  Attribute::Dereferenceable);
                      newAttrList = newAttrList.addAttribute(
                          call_inst->getContext(),
                          1, // the index of the parameter to modify (1-based)
                          Attribute::getWithDereferenceableBytes(call_inst->getContext(), derefer));  
                      call_inst->setAttributes(newAttrList);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    for (auto& inst : changed_insts)
    {
      ReplaceUnsafe(inst.second,inst.first);
      inst.second->eraseFromParent();
    }
    for (auto&F : M)
    {
      if (F.getLinkage() == GlobalValue::LinkageTypes::InternalLinkage)
      {
        F.setDSOLocal(true);
      }
    }
    std::vector<GlobalVariable*> gv_to_delete;
    for (auto& it : old_to_new_variable)
    {
      if (it.first->use_empty())
      {
        it.first->eraseFromParent();
      }
      else
      {
        auto cur = it.first->use_begin();
        GlobalVariable *GV = new GlobalVariable(
          /* Module */ M,
          /* Type */ it.first->getValueType(),
          /* isConstant */ false,
          /* Linkage */ GlobalValue::ExternalLinkage,
          /* Initializer */ nullptr,
          /* Name */ "",
          nullptr,
          GlobalValue::ThreadLocalMode::NotThreadLocal,
          it.first->getAddressSpace(),
          false
        );
        it.first->replaceAllUsesWith(GV);
        it.first->eraseFromParent();
        gv_to_delete.push_back(GV);
      }
    }
    for (auto& i : gv_to_delete)
    {
      i->eraseFromParent();
    }
    // Erase functions we dont need?
    for (auto& old_fun : functions_to_fix_later)
    {
      if (old_fun->getParent()) 
      {
        Function* test_function=real_to_fake_functions[old_fun];
        ReplaceUnsafe(old_fun, test_function);
        old_fun->eraseFromParent();
      }
    }
    // We have left some functions hanging - just delete them 
    std::unordered_set<Instruction*> inst_to_del;
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {      
          if (auto alloca_inst = dyn_cast<AllocaInst>(&I))
          {
            if (alloca_inst->getType()->getPointerAddressSpace()!=200)
            {
              inst_to_del.insert(alloca_inst);  
            }
          }
        }
      }
    }
    for (auto& inst : inst_to_del)
    {
      if (inst->use_empty())
      {
        inst->eraseFromParent();
      }
    }
    std::vector<Instruction*> ins_to_delete_for_cap;
    // We have to change the diff of casts to a real diff
    for (auto& F : M) 
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto binary_op = dyn_cast<BinaryOperator>(&I))
          {
            if (binary_op->getOpcode() == llvm::Instruction::Sub)
            {
              auto op1 = I.getOperand(0);
              auto op2 = I.getOperand(1);
              if (isa<Instruction>(op1) && isa<Instruction>(op2))
              {
                auto ins_op1 = dyn_cast<CallInst>(op1);
                auto ins_op2 = dyn_cast<CallInst>(op2);
                if (ins_op1 && ins_op2)
                {
                  auto name1 = ins_op1->getCalledFunction()->getName().str();
                  auto name2 = ins_op2->getCalledFunction()->getName().str();
                  if (name1=="llvm.cheri.cap.address.get.i64" && name2=="llvm.cheri.cap.address.get.i64")
                  {
                    // Make a cap.diff function
                    auto id = Function::lookupIntrinsicID("llvm.cheri.cap.diff.i64");
                    auto i8_type = Type::getInt8Ty(M.getContext());
                    auto i64_type = Type::getInt64Ty(M.getContext());
                    PointerType* i8PtrType = i8_type->getPointerTo(200);
                    std::vector<Type*> types;
                    types.push_back(i64_type);
                    auto instrisic_function = Intrinsic::getDeclaration(&M,id,ArrayRef<Type*>(types));
                    std::vector<Value*> arguments;
                    arguments.push_back(ins_op1->getOperand(0));
                    arguments.push_back(ins_op2->getOperand(0));
                    ArrayRef<Value*> args(arguments);
                    CallInst* call_inst = CallInst::Create(instrisic_function->getFunctionType(),instrisic_function,args,"",&I);
                    I.replaceAllUsesWith(call_inst);
                    if (ins_op1->getNumUses()<=1) ins_to_delete_for_cap.push_back(ins_op1);
                    if (ins_op2->getNumUses()<=1)ins_to_delete_for_cap.push_back(ins_op2);
                    ins_to_delete_for_cap.push_back(&I);
                  }
                }
              }
            }
          }
        }
      }
    }

    reverse(ins_to_delete_for_cap.begin(),ins_to_delete_for_cap.end());
    for (auto& ins : ins_to_delete_for_cap)
    {
      ins->eraseFromParent();
    }

    // Fix call functions - second time
    fixCallFunctions(M);
    // WORKS
    // might-work3
    // Solve global va_args dependant arguments
    std::unordered_map<GlobalVariable*, GlobalVariable*> map_of_va_global_values;
    std::unordered_set<GlobalVariable*> delete_gv_for_vaarg;
    std::unordered_set<GlobalVariable*> new_changed_global_variables_for_vaargs;
    for (auto& F : M) 
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          for (int i=0;i<I.getNumOperands();i++)
          {
            auto op = I.getOperand(i);
            if (isa<GlobalVariable>(op) && check_if_type_to_va_list_for_globals(op->getType()))
            {
              GlobalVariable* my_gv = dyn_cast<GlobalVariable>(op);
              if (map_of_va_global_values.find(my_gv)==map_of_va_global_values.end())
              {
                GlobalVariable* gv = change_global_variable_for_va_arg(my_gv);
                map_of_va_global_values[my_gv]=gv;
                new_changed_global_variables_for_vaargs.insert(gv);
                delete_gv_for_vaarg.insert(my_gv);
              }
              I.setOperand(i,map_of_va_global_values[my_gv]);
            }
          }
        }
      }
    }
    for (auto gv : delete_gv_for_vaarg)
    {
      gv->eraseFromParent();
    }
    std::unordered_map<Instruction*,Instruction*> temp_va_instructions; 
    std::vector<Instruction*> delete_for_va;
    // Now, we fix the variable argument functions
    std::unordered_map<Value*,Value*> va_list_instructions;
    Instruction* helper_inst = nullptr;
    std::unordered_map<Function*, Value*> byval_temp_of_function;

    for (auto& F : M) // we find all va_allocas
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {      
          if (auto all_inst = dyn_cast<AllocaInst>(&I))
          {
            PointerType* pt = (PointerType*)(all_inst->getType());
            Type* t = pt->getElementType();
            bool is_direct=false;
            if (isa<StructType>(t))
            {
              StructType* st = dyn_cast<StructType>(t);
              if (!st->isLiteral() && st->getName().str()=="struct.__va_list")
              {
                is_direct=true;
                // If it needs to be here
                if (!is_prefix(I.getName().str(),"byval-temp"))
                {
                  Type *PointerType = Type::getInt8PtrTy(M.getContext(), 200); 
                  auto name_k = I.getName().str();
                  I.setName("");
                  AllocaInst* new_all_inst = new AllocaInst(PointerType, 200, nullptr, Align(16), name_k, &I);
                  va_list_instructions[&I]=new_all_inst;
                  va_list_instructions[new_all_inst]=new_all_inst;
                  helper_inst = new_all_inst;
                  delete_for_va.push_back(&I);
                }
                else
                {
                  temp_va_instructions[&I]=helper_inst;
                  delete_for_va.push_back(&I);
                }
              }
            }
            if (!is_direct && check_if_type_to_va_list_for_globals(pt))
            {
              Type* changed_type = change_from_va_type_for_globals(t);
              auto name_k = I.getName().str();
              I.setName("");
              AllocaInst* new_all_inst = new AllocaInst(changed_type, 200, nullptr, Align(16), name_k, &I);
              va_list_instructions[&I]=new_all_inst;
              helper_inst = new_all_inst;
              delete_for_va.push_back(&I);
            }
          }
        }
      }
    }

    // Might be a global variable which can also be used for this - see stdarg-1.c
    for (auto& global : new_changed_global_variables_for_vaargs)
    {
      PointerType* pt = (PointerType*)(global->getType());
      if (pt->getElementType()->isPointerTy())
      {
        auto i8_type = Type::getInt8Ty(whole_module->getContext());
        PointerType* i8PtrType = i8_type->getPointerTo(200);
        if (pt->getElementType()==i8PtrType)
        {
          va_list_instructions[global]=global;
        }
      }
    }

    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {  
          if (auto load_inst = dyn_cast<LoadInst>(&I))
          {
            if (isa<GlobalVariable>(load_inst->getOperand(0)))
            {
              GlobalVariable* op = dyn_cast<GlobalVariable>(load_inst->getOperand(0));
              if (new_changed_global_variables_for_vaargs.find(op)!=new_changed_global_variables_for_vaargs.end())
              {
                PointerType* pt = (PointerType*)op->getType();
                I.mutateType(pt->getElementType());
                va_list_instructions[&I]=&I;
              }
            }
          }
        }
      }
    }

    std::unordered_set<Instruction*> what_to_delete;
    std::unordered_set<Instruction*> added_loads; // Might be helpful to fix if there are any function that just pass va_lists;
    std::unordered_map<Value*,Value*> byvals_to_copied_values;

    for (auto& F : M) // subsitute for before var_args
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {  
          if (auto getelementptr_inst = dyn_cast<GetElementPtrInst>(&I))
          {
            auto first_op = dyn_cast<Instruction>(getelementptr_inst->getOperand(0));
            if (va_list_instructions.find(first_op)!=va_list_instructions.end())
            {
              I.setOperand(0,va_list_instructions[first_op]);
              Type* t = I.getType();
              Type* changed_type = change_from_va_type_for_globals(t);
              Type* new_results_element_type = change_from_va_type_for_globals(getelementptr_inst->getResultElementType());
              I.mutateType(changed_type);
              getelementptr_inst->setSourceElementType(((PointerType*)va_list_instructions[first_op]->getType())->getElementType());
              getelementptr_inst->setResultElementType(new_results_element_type);
              va_list_instructions[&I]=&I;
            }
          }
          if (auto bitcast_inst = dyn_cast<BitCastInst>(&I))
          {
            auto first_op = dyn_cast<Instruction>(bitcast_inst->getOperand(0));
            if (va_list_instructions.find(first_op)!=va_list_instructions.end())
            {
              I.setOperand(0,va_list_instructions[first_op]);
            }
            if (temp_va_instructions.find(first_op)!=temp_va_instructions.end())
            {
              what_to_delete.insert(&I);
              delete_for_va.push_back(&I);
            }
          } 
          if (auto store_inst = dyn_cast<StoreInst>(&I))
          {
            auto first_op = dyn_cast<Instruction>(store_inst->getOperand(0));
            if (va_list_instructions.find(first_op)!=va_list_instructions.end())
            {
              I.setOperand(0,va_list_instructions[first_op]);
            }
            if (temp_va_instructions.find(first_op)!=temp_va_instructions.end())
            {
              what_to_delete.insert(&I);
              delete_for_va.push_back(&I);
            }
          } 
          if (auto call_inst = dyn_cast<CallInst>(&I))
          {
            if (call_inst->getCalledFunction() && is_prefix(call_inst->getCalledFunction()->getName().str(),"llvm.memcpy"))
            {
              if (auto int_cast = dyn_cast<Instruction>(call_inst->getArgOperand(0)))
              {
                if (auto bitcast_int_cast = dyn_cast<BitCastInst>(int_cast))
                {
                  if (is_prefix(bitcast_int_cast->getOperand(0)->getName().str(),"byval-temp"))
                  {
                    if (auto second = dyn_cast<BitCastInst>(call_inst->getArgOperand(1)))
                    {
                      byvals_to_copied_values[bitcast_int_cast->getOperand(0)]=second->getOperand(0);
                    }
                  }
                }
              }
            }
            for (unsigned int i = 0; i < call_inst->getNumArgOperands(); i++) 
            {
              Instruction* instruction_param = dyn_cast<Instruction>(call_inst->getArgOperand(i));
              if (instruction_param)
              {
                if (temp_va_instructions.find(instruction_param)!=temp_va_instructions.end())
                {
                  auto i8_type = Type::getInt8Ty(whole_module->getContext());
                  PointerType* i8PtrType = i8_type->getPointerTo(200);
                  LoadInst* ld;
                  if (byvals_to_copied_values.find(instruction_param)!=byvals_to_copied_values.end()) // something copied into byval
                  {
                    // We need to make address, if that is needed
                    if (byvals_to_copied_values[instruction_param]->getType()==i8PtrType)
                    {
                      AllocaInst* alloca_inst = new AllocaInst(i8PtrType,200,byvals_to_copied_values[instruction_param]->getName()+".addr",&I);
                      StoreInst* store_inst = new StoreInst(byvals_to_copied_values[instruction_param],alloca_inst,&I);
                      ld = new LoadInst(i8PtrType, alloca_inst,"",&I);
                    }
                    else ld = new LoadInst(i8PtrType, byvals_to_copied_values[instruction_param],"",&I);
                  }
                  else ld = new LoadInst(i8PtrType, temp_va_instructions[instruction_param],"",&I);
                  added_loads.insert(ld);
                  I.setOperand(i,ld);
                }
                if (what_to_delete.find(instruction_param)!=what_to_delete.end())
                {
                  delete_for_va.push_back(&I);
                }
              }
            }
          }
        }
      }
    }
    std::unordered_map<Value*,Value*> is_in_getelementptr;
    bool started_var_arg_checks=false;
    bool finishing_up_arg_checks = false;
    bool final_arg_checks = false;
    bool is_in_function_for_just_passing_var_arguments = false;
    Value* its_arguments;
    Instruction* stack_inst;
    Instruction* new_bitcast;
    Instruction* elementptr_in_front_of_bitcast;
    std::vector<BasicBlock*> delete_bb;
    BasicBlock* basic_block;
    std::unordered_map<BasicBlock*,std::vector<Instruction*>> instructions_to_switch_basic_block;
    std::vector<Instruction*> instructions_to_change; 
    std::unordered_set<Function*> new_functions_with_changed_vararg;
    std::unordered_map<Value*,Value*> already_made_alloca_functions;
    Instruction* first_inst_of_function = nullptr;
    std::unordered_map<Value*, Value*> mapping_for_just_passing_va_arguments;
    std::unordered_map<Instruction*, BasicBlock*> basic_block_for_every_instruction;
    std::unordered_map<Value*,Value*> vals_to_allocainsts;
    for (auto& func : changed_functions_for_vararg)
    {
      new_functions_with_changed_vararg.insert(real_to_fake_functions[func]);
    }
    std::vector<Function*> old_functions_for_va_change;
    for (auto& changed : old_changed_for_va_arguments)
    {
      old_functions_for_va_change.push_back(changed.first);
    }
    std::unordered_map<Function*,std::unordered_set<int>> new_changed_for_va_arguments;
    for (auto& old_func : old_functions_for_va_change)
    {
      new_changed_for_va_arguments[real_to_fake_functions[old_func]]=old_changed_for_va_arguments[old_func];
    }
    for (auto& F : M) 
    {
      started_var_arg_checks=false;
      finishing_up_arg_checks = false;
      final_arg_checks = false;
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          basic_block_for_every_instruction[&I]=&B;  
          if (!first_inst_of_function) first_inst_of_function=&I;
          if (auto element_inst = dyn_cast<GetElementPtrInst>(&I)) // find the first getelementptr that might start the maybe_vaarg and maybe_stack
          {
            if (B.getNextNode() && is_prefix(B.getNextNode()->getName().str(),"vaarg.maybe_reg") && (is_prefix(I.getName().str(),"vr_offs") || is_prefix(I.getName().str(),"gr_offs")))
            {
              auto first_op = element_inst->getOperand(0);
              // when not used in argument
              bool is_valid_vaarg = (!is_prefix(B.getName().str(),"vaarg")) || (is_prefix(B.getName().str(),"vaarg.end"));
              if (va_list_instructions.find(first_op)!=va_list_instructions.end() && is_in_getelementptr.find(first_op)==is_in_getelementptr.end() && is_valid_vaarg)
              {
                started_var_arg_checks=true;
                final_arg_checks=false;
                its_arguments = va_list_instructions[first_op];
                if (!is_prefix(B.getName().str(),"vaarg"))
                {
                  basic_block=&B;
                }
              }
              // when used in argument
              else if (!started_var_arg_checks && !finishing_up_arg_checks) 
              {
                if (true || new_functions_with_changed_vararg.find(&F)!=new_functions_with_changed_vararg.end())
                {
                  if (auto struct_elem_type = dyn_cast<StructType>(element_inst->getSourceElementType()))
                  {
                    if (struct_elem_type->getName().str()=="struct.__va_list")
                    {
                      started_var_arg_checks=true;
                      final_arg_checks=false;
                      std::vector<Instruction*> added_inst;
                      // Now we make a pointer to a pointer of variable argument list (or another pointer)
                      if (already_made_alloca_functions.find(element_inst->getOperand(0))==already_made_alloca_functions.end())
                      {
                        // Maybe the pointer was already made? 
                        auto new_set_of_changed_params = new_changed_for_va_arguments[&F];
                        bool exists_as_param = false;
                        for (auto& param_num : new_set_of_changed_params)
                        {
                          if (element_inst->getOperand(0)==F.getArg(param_num))
                          {
                            exists_as_param=true;
                          }
                        }
                        if (exists_as_param)
                        {
                          Type* i8PtrType = PointerType::get(IntegerType::get(M.getContext(), 8), 200);
                          AllocaInst* allocaInst = new AllocaInst(i8PtrType, 200, element_inst->getOperand(0)->getName().str()+".addr", first_inst_of_function);               
                          StoreInst* store_inst = new StoreInst(element_inst->getOperand(0),allocaInst,first_inst_of_function);
                          already_made_alloca_functions[element_inst->getOperand(0)]=allocaInst;
                          its_arguments = already_made_alloca_functions[element_inst->getOperand(0)];
                        }
                        else
                        {
                          Type* i8PtrType = PointerType::get(IntegerType::get(M.getContext(), 8), 200);
                          Value* val = byvals_to_copied_values[element_inst->getOperand(0)];
                          if (val && byvals_to_copied_values.find(val)!=byvals_to_copied_values.end()) // is a byval
                          {
                            val = vals_to_allocainsts[byvals_to_copied_values[val]];
                          }
                          if (val && val->getType()!=i8PtrType)
                          {
                            AllocaInst* allocaInst = new AllocaInst(i8PtrType, 200, val->getName().str()+".addr", first_inst_of_function);    
                            Instruction* val_inst = dyn_cast<Instruction>(val);
                            if (val_inst)
                            {
                              Instruction* next_inst = val_inst->getNextNode();
                              LoadInst* load_inst = new LoadInst(i8PtrType,val,"",&I);
                              byvals_to_copied_values[element_inst->getOperand(0)]=load_inst;
                              vals_to_allocainsts[load_inst]=allocaInst;
                              added_inst.push_back(load_inst);
                              StoreInst* store_inst = new StoreInst(load_inst,allocaInst,&I);
                              added_inst.push_back(store_inst);
                            }
                            else
                            {
                              LoadInst* load_inst = new LoadInst(i8PtrType,val,"",first_inst_of_function);
                              byvals_to_copied_values[element_inst->getOperand(0)]=load_inst;
                              vals_to_allocainsts[load_inst]=allocaInst;
                              StoreInst* store_inst = new StoreInst(load_inst,allocaInst,first_inst_of_function);
                            }
                            already_made_alloca_functions[val]=allocaInst;
                            its_arguments = already_made_alloca_functions[val];
                          }
                          else if (val)
                          {
                            Value* allocaInst;
                            if (vals_to_allocainsts.find(val)!=vals_to_allocainsts.end()) allocaInst=vals_to_allocainsts[val];
                            else allocaInst = new AllocaInst(i8PtrType, 200, val->getName().str()+".addr", first_inst_of_function);    
                            Instruction* val_inst = dyn_cast<Instruction>(val);
                            already_made_alloca_functions[val]=allocaInst;
                            its_arguments = already_made_alloca_functions[val];
                          }
                          else
                          {
                            // This is probably an error
                          }
                          // FILL THIS
                        }
                      }
                      else 
                      {
                        its_arguments = already_made_alloca_functions[element_inst->getOperand(0)];
                      }
                      if (!is_prefix(B.getName().str(),"vaarg"))
                      {
                        basic_block=&B;
                      }
                      for (Instruction* inst : added_inst)
                      {
                        instructions_to_switch_basic_block[basic_block].push_back(inst);
                      }
                    }
                  }
                }
              }
            }
          } 
          // There is another translation that needs to be done - if we are just doing it for the sake of passing on the va_list
          if (!started_var_arg_checks && !finishing_up_arg_checks && !final_arg_checks)
          {
            if (new_functions_with_changed_vararg.find(&F)!=new_functions_with_changed_vararg.end())
            {
              if (auto bitcast_inst = dyn_cast<BitCastInst>(&I))
              {
                // Change what parameter it is
                for (int i=0;i<bitcast_inst->getNumOperands();i++)
                {
                  if (new_changed_for_va_arguments.find(&F)!=new_changed_for_va_arguments.end())
                  {
                    auto new_set_of_changed_params = new_changed_for_va_arguments[&F];
                    for (auto& param_num : new_set_of_changed_params)
                    {
                      if (bitcast_inst->getOperand(i)==F.getArg(param_num))
                      {
                        // We found something that we need to change (a parameter that was for variable arguments, but now has changed)
                        if (already_made_alloca_functions.find(bitcast_inst->getOperand(i))==already_made_alloca_functions.end())
                        {  
                          Type* i8PtrType = PointerType::get(IntegerType::get(M.getContext(), 8), 200);
                          AllocaInst* allocaInst = new AllocaInst(i8PtrType, 200, bitcast_inst->getOperand(i)->getName().str()+".addr", first_inst_of_function);
                          StoreInst* store_inst = new StoreInst(bitcast_inst->getOperand(i),allocaInst,first_inst_of_function);
                          already_made_alloca_functions[bitcast_inst->getOperand(i)]=allocaInst;
                          is_in_function_for_just_passing_var_arguments=true;
                        }
                        mapping_for_just_passing_va_arguments[bitcast_inst->getOperand(i)]=already_made_alloca_functions[bitcast_inst->getOperand(i)];
                        its_arguments = already_made_alloca_functions[bitcast_inst->getOperand(i)];
                      }
                    }
                  }
                }
              }
              if (is_in_function_for_just_passing_var_arguments)
              {
                // For now only for load, we'll se for what else
                if (added_loads.find(&I)!=added_loads.end())
                {
                  I.setOperand(0,its_arguments);
                }
              }
            }
          }
          if (started_var_arg_checks)
          {
            if (is_prefix(B.getName().str(),"vaarg.on_stack")) // here it ends
            {
              I.replaceAllUsesWith(its_arguments);
              started_var_arg_checks=false;
              finishing_up_arg_checks=true;
            }
            delete_for_va.push_back(&I);
          }
          else if (finishing_up_arg_checks)
          {
            if (auto load_inst = dyn_cast<LoadInst>(&I))
            {
              stack_inst=&I;
              instructions_to_switch_basic_block[basic_block].push_back(&I);
            } 
            else if (auto element_inst = dyn_cast<GetElementPtrInst>(&I))
            {
              // Change alignement
              Type* i64Type = Type::getInt64Ty(M.getContext());
              Constant* const16 = ConstantInt::get(i64Type, 16);
              element_inst->setOperand(1,const16);
              elementptr_in_front_of_bitcast = &I;
              instructions_to_switch_basic_block[basic_block].push_back(&I);
            } 
            else if (auto bitcast_inst = dyn_cast<BitCastInst>(&I))
            {
              Type* my_type = bitcast_inst->getType();
              BitCastInst* new_bitcast_inst = new BitCastInst(stack_inst, my_type, "", elementptr_in_front_of_bitcast);
              new_bitcast=new_bitcast_inst;
              instructions_to_switch_basic_block[basic_block].push_back(new_bitcast_inst);
              delete_for_va.push_back(&I);
            }
            else if (isa<PHINode>(&I))
            {
              I.replaceAllUsesWith(new_bitcast);
              delete_for_va.push_back(&I);
              finishing_up_arg_checks=false;
              final_arg_checks = true;
              Instruction* next_instruction = I.getNextNode();
              if (auto load_next_inst = dyn_cast<LoadInst>(next_instruction))
              {
                load_next_inst->setAlignment(Align(16));
              }
            }
            else if (auto branch_inst = dyn_cast<BranchInst>(&I))
            {
              if (is_prefix(branch_inst->getSuccessor(0)->getName().str(),"vaarg.end") || ends_with(branch_inst->getSuccessor(0)->getName().str(),".exit"))
              {
                delete_for_va.push_back(&I);
              }
              else
              {
                instructions_to_switch_basic_block[basic_block].push_back(&I); 
              }
            }
            else
            {
              instructions_to_switch_basic_block[basic_block].push_back(&I);
            }
          }
          else if (final_arg_checks)
          {
            if (I.isTerminator())
            {
              final_arg_checks=false;
            }
            instructions_to_switch_basic_block[basic_block].push_back(&I);
          }
        }
      }
      first_inst_of_function=nullptr;
      is_in_function_for_just_passing_var_arguments=false;
    }
    std::unordered_map<BasicBlock*, BasicBlock*> blocks_to_map_phi_nodes;
    for (auto& basic : instructions_to_switch_basic_block)
    {
      for (auto& insts : basic.second)
      {
        blocks_to_map_phi_nodes[basic_block_for_every_instruction[insts]]=basic.first;
        insts->removeFromParent();
        basic.first->getInstList().push_back(insts);
      }
    }
    reverse(delete_for_va.begin(),delete_for_va.end());
    std::unordered_set<Instruction*> del_val;
    for (auto p : delete_for_va)
    {
      del_val.insert(p);
    }
    while (del_val.size()>0)
    {
      std::unordered_set<Instruction*> del_val2;
      for (auto p : del_val)
      {
        Instruction* ins = p;
        if (ins->use_empty()) 
        {
          ins->eraseFromParent();
          del_val2.insert(ins);
        }
      }
      for (auto k : del_val2)
      {
        del_val.erase(k);
      }
    }

    // Fixing the PHI nodes
    for (auto& F : M) 
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto phi_node = dyn_cast<PHINode>(&I))
          {
            for (int i=0;i<phi_node->getNumIncomingValues();i++)
            {
              BasicBlock* inc = phi_node->getIncomingBlock(i);
              if (blocks_to_map_phi_nodes.find(inc)!=blocks_to_map_phi_nodes.end())
              {
                phi_node->setIncomingBlock(i,blocks_to_map_phi_nodes[inc]);
              }
            }
          }
        }
      }
    }    

    // Fix getElementPtr for vaargs
    std::unordered_map<Instruction*, Value*> vals_to_map;
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto elemPtrInst = dyn_cast<GetElementPtrInst>(&I))
          {
            auto op = elemPtrInst->getOperand(0);
            if (isa<GlobalVariable>(elemPtrInst->getOperand(0)))
            {
              GlobalVariable* op = dyn_cast<GlobalVariable>(elemPtrInst->getOperand(0));
              if (new_changed_global_variables_for_vaargs.find(op)!=new_changed_global_variables_for_vaargs.end())
              {
                vals_to_map[&I]=op;
              }
            }
          }
        }
      }
    }

    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          for (int i=0;i<I.getNumOperands();i++)
          {
            auto op = I.getOperand(i);
            if (auto ins = dyn_cast<Instruction>(op))
            {
              if (vals_to_map.find(ins)!=vals_to_map.end())
              {
                I.setOperand(i, vals_to_map[ins]);
              }
            }
          }
        }
      }
    }

    for (auto& vals : vals_to_map)
    {
      vals.first->eraseFromParent();
    }

    for (auto& F : M) 
    {
      for (auto& B : F)
      {
        if (B.size()==0) 
        {
          delete_bb.push_back(&B);
        }
      }
    }

    std::unordered_map<Value*, Value*> something_else_to_pick;
    std::vector<Instruction*> delete_something_else;
    // We recognize ptrtoint-add-and-inttoptr - this signifies stack alignment (which is bad) - needs to be deleted
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto callInst = dyn_cast<CallInst>(&I))
          {
            Instruction* next1 = I.getNextNode();
            if (next1)
            {
              Instruction* next2 = next1->getNextNode();
              if (next2)
              {
                Instruction* next3 = next2->getNextNode();
                if (next3)
                {
                  if (isa<BinaryOperator>(next1) && isa<BinaryOperator>(next2) && isa<GetElementPtrInst>(next3))
                  {
                    if (callInst->getCalledFunction() && callInst->getCalledFunction()->getName().str()=="llvm.cheri.cap.address.get.i64")
                    {
                      auto getptr3 = dyn_cast<GetElementPtrInst>(next3);
                      auto getptr2 = dyn_cast<BinaryOperator>(next2);
                      auto getptr1 = dyn_cast<BinaryOperator>(next1);
                      auto op1 = getptr3->getOperand(0);
                      auto andop1 = getptr3->getOperand(1);
                      auto addop1 = getptr1->getOperand(1);
                      if (isa<ConstantInt>(addop1) && isa<ConstantInt>(andop1) && isa<ConstantPointerNull>(op1))
                      {
                        auto val2 = dyn_cast<ConstantInt>(andop1);
                        if (val2->getSExtValue()==16) // why not -16?
                        {
                          something_else_to_pick[next3]=I.getOperand(0);
                          delete_something_else.push_back(&I);
                          delete_something_else.push_back(next1);
                          delete_something_else.push_back(next2);
                          delete_something_else.push_back(next3);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          for (int i=0;i<I.getNumOperands();i++)
          {
            auto op = I.getOperand(i);
            if (auto ins = dyn_cast<Instruction>(op))
            {
              if (something_else_to_pick.find(ins)!=something_else_to_pick.end())
              {
                I.setOperand(i, something_else_to_pick[ins]);
              }
            }
          }
        }
      }
    }

    reverse(delete_something_else.begin(),delete_something_else.end());

    for (auto& vals : delete_something_else)
    {
      vals->eraseFromParent();
    }

    for (int i=0;i<delete_bb.size();i++)
    {
      delete_bb[i]->eraseFromParent();
    }

    // Fix sizeof - find all add sizes
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (I.getOpcode() == Instruction::Add)
          {
            if (auto md = I.getMetadata("sizeof"))
            {
              if (isa<Metadata>(md->getOperand(0).get()))
              {
                Metadata* m = md->getOperand(0).get();
                if (auto md_node = dyn_cast<MDNode>(m))
                {
                  if (auto md_string = dyn_cast<MDString>(md_node->getOperand(0).get()))
                  {
                    auto str_value = md_string->getString().str();
                    int size_cheri = get_size_from_string(str_value, true);
                    int size_no_cheri = get_size_from_string(str_value, false);
                    if (size_cheri!=-1 && size_cheri!=size_no_cheri)
                    {
                      ConstantInt* c1 = dyn_cast<ConstantInt>(I.getOperand(0));
                      int last_val = c1->getValue().getSExtValue();
                      last_val*=size_cheri;
                      last_val/=size_no_cheri;
                      ConstantInt* const_int = ConstantInt::get(M.getContext(), APInt(64, last_val));  
                      I.setOperand(0,const_int);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    // Now we deal with uintptr_t and intptr_t
    /*
      We need to change it from i64 to i8* addrspace(200)
      No longer any need to call values_of_allocated_uinptrs_allocas
      bitcast instead of getelementptr
    */
    std::unordered_map<Value*,Value*> values_of_allocated_uinptrs_allocas;
    std::unordered_map<Value*,Value*> second_map;
    std::unordered_set<Instruction*> to_delete_for_intptr;
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (isa<AllocaInst>(&I))
          {
            if (auto md = I.getMetadata("intptr_t"))
            {
              llvm::Type* ptr_type = llvm::PointerType::get(llvm::Type::getInt8Ty(M.getContext()), 200);
              std::string name = I.getName().str();
              I.setName("");
              AllocaInst* al_inst = new AllocaInst(ptr_type, 200, name, &I);
              values_of_allocated_uinptrs_allocas[&I]=al_inst;
              to_delete_for_intptr.insert(&I);
            }
          }
        }
      }
    }

    // If we're trying to store the old intptr_t instead of the new one 
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto store_inst = dyn_cast<StoreInst>(&I))
          {
            auto operand_0 = store_inst->getOperand(0);
            if (auto inst = dyn_cast<Instruction>(operand_0))
            {
              if (auto call_inst = dyn_cast<CallInst>(inst))
              {
                if (Function* calledFunction = call_inst->getCalledFunction())
                {
                  // If we have gotten this from get, substitute it
                  if (calledFunction->getName()=="llvm.cheri.cap.address.get.i64")
                  {
                    auto second_op = store_inst->getOperand(1);
                    if (values_of_allocated_uinptrs_allocas.find(second_op)!=values_of_allocated_uinptrs_allocas.end())
                    {
                      store_inst->setOperand(0,call_inst->getArgOperand(0));
                      store_inst->setOperand(1,values_of_allocated_uinptrs_allocas[second_op]);
                      store_inst->setAlignment(Align(16));
                      to_delete_for_intptr.insert(call_inst);
                    }
                  }
                }
              }
            }
          }
          if (auto getelem_inst = dyn_cast<GetElementPtrInst>(&I)) // this is actually inttoptr
          {
            if (isa<ConstantPointerNull>(I.getOperand(0)))
            {
              auto operand_1 = I.getOperand(1);
              if (auto load_inst = dyn_cast<LoadInst>(operand_1))
              {
                auto second_op = load_inst->getOperand(0);
                if (values_of_allocated_uinptrs_allocas.find(second_op)!=values_of_allocated_uinptrs_allocas.end())
                {
                  Type* i8PtrType = Type::getInt8PtrTy(M.getContext(), 200);
                  std::string name = I.getName().str();
                  I.setName("");
                  // Also change the load instruction
                  load_inst->setOperand(0,values_of_allocated_uinptrs_allocas[second_op]);
                  load_inst->mutateType(i8PtrType);
                  load_inst->setAlignment(Align(16));
                  Value* bitcastInst = new BitCastInst(load_inst, I.getType(), "", &I);
                  second_map[&I]=bitcastInst;
                  to_delete_for_intptr.insert(&I);
                }
              }
            }
          }
        }
      }
    }
    std::unordered_map<Value*,Value*> to_cheri_get_address;
    std::unordered_set<Value*> do_not_change;
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          for (int i=0;i<I.getNumOperands();i++)
          {
            Value* new_val=nullptr;
            Value* old_val=I.getOperand(i);
            if (values_of_allocated_uinptrs_allocas.find(I.getOperand(i))!=values_of_allocated_uinptrs_allocas.end())
            {
              new_val = values_of_allocated_uinptrs_allocas[I.getOperand(i)];
            }
            else if (second_map.find(I.getOperand(i))!=second_map.end())
            {
              new_val = second_map[I.getOperand(i)];
            }
            if (new_val)
            {
              I.setOperand(i,new_val);
              // If we need to change the alignment of loads/stores, as well as change the load
              if (auto ld_inst = dyn_cast<LoadInst>(&I))
              {
                auto typ = ((PointerType*)(new_val->getType()))->getElementType();
                ld_inst->mutateType(typ);
                // Add cheri get type
                if (values_of_allocated_uinptrs_allocas.find(old_val)!=values_of_allocated_uinptrs_allocas.end())
                {
                  auto id = Function::lookupIntrinsicID("llvm.cheri.cap.address.get.i64");
                  auto i64_type = Type::getInt64Ty(M.getContext());
                  std::vector<Type*> over_types;
                  over_types.push_back(i64_type);
                  std::vector<Value*> arguments;
                  arguments.push_back(&I);
                  auto instrisic_function = Intrinsic::getDeclaration(&M,id,ArrayRef<Type*>(over_types));
                  auto name = I.getName().str();
                  I.setName("");
                  ArrayRef<Value*> args(arguments);
                  CallInst* call_inst = CallInst::Create(instrisic_function->getFunctionType(),instrisic_function,args,name,I.getNextNode());
                  to_cheri_get_address[&I]=call_inst;
                  do_not_change.insert(call_inst);
                }
                if (isa<PointerType>(typ))
                {
                  ld_inst->setAlignment(Align(16));
                }
              }
              if (auto store_inst = dyn_cast<StoreInst>(&I))
              {
                auto first_type = I.getOperand(0)->getType();
                if (isa<PointerType>(first_type))
                {
                  store_inst->setAlignment(Align(16));
                }
              }
            }
          }
        }
      }
    }

    // Fix to cheri get address
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          for (int i=0;i<I.getNumOperands();i++)
          {
            auto op = I.getOperand(i);
            if (to_cheri_get_address.find(op)!=to_cheri_get_address.end() && do_not_change.find(&I)==do_not_change.end())
            {
              if (auto store_inst = dyn_cast<StoreInst>(&I))
              {
                if (i==0)
                {
                  if (isa<PointerType>(store_inst->getOperand(1)->getType()))
                  {
                    // If pointers already match
                    PointerType* pt_type = (PointerType*)(store_inst->getOperand(1)->getType());
                    if (pt_type->getElementType()==op->getType()) continue;
                  }
                }
              }
              I.setOperand(i,to_cheri_get_address[op]);
            }
          }
        }
      }
    }

    for (auto k : to_delete_for_intptr)
    {
      k->eraseFromParent();
    }

    // Fix some of the coerced types
    std::unordered_map<Argument*,StructType*> coarsced_parameters;
    for (auto& F : M)
    {
      for (auto &A : F.getAttributes())
      {
        for (auto& attr : A)
        {
          if (attr.isStringAttribute())
          {
            auto value = attr.getValueAsString().str();
            std::string f = "coarced";
            if (value.find(f)==0) // starts with coarced
            {
              std::vector<std::string> strings = split_string(value,"#");
              std::string name = strings[1];
              std::string type = strings[2];
              for (auto AI = F.arg_begin(), AE = F.arg_end(); AI != AE; ++AI) 
              {
                Argument* arg = &*AI;
                if (arg->getName()==name)
                {
                  Value* val = arg;
                  // Get type
                  std::vector<std::string> type_string = split_string(type," ");
                  // Check if it is a struct
                  if (type_string.size()>1 && type_string[0]=="struct")
                  {
                    StructType* st = StructType::getTypeByName(M.getContext(),"struct."+type_string[1]);
                    if (st && struct_has_pointer(st) && isa<ArrayType>(arg->getType()))
                    {
                      coarsced_parameters[arg]=st;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    std::unordered_map<Argument*,StructType*> withLiteralStructTypes;
    std::unordered_set<Instruction*> to_delete;
    std::unordered_map<Function*,StructType*> functions_to_change;
    // Now for actually changing the thing
    for (auto& vals : coarsced_parameters)
    {
      Argument* arg = vals.first;
      StructType* st = vals.second;
      StructType* literal_struct = StructType::get(whole_module->getContext(),st->elements(),st->isPacked());
      withLiteralStructTypes[arg]=literal_struct;
      arg->mutateType(literal_struct);
      // Finding the first store
      Function* f = arg->getParent();
      for (auto& B : *f)
      {
        for (auto& I : B)
        {
          {
            if (auto store_inst = dyn_cast<StoreInst>(&I))
            {
              if (store_inst->getOperand(0)==arg)
              {
                // This probably came from bitcast, we need to replace that one
                if (auto bitcast_inst = dyn_cast<BitCastInst>(store_inst->getOperand(1)))
                {
                  PointerType* pt = PointerType::get(literal_struct,200);
                  bitcast_inst->mutateType(pt);
                  // Make the instructions
                  int cnt = 0;
                  int align = get_alignment(literal_struct,true);
                  for (auto element : literal_struct->elements())
                  {
                    Value* zero = ConstantInt::get(Type::getInt32Ty(whole_module->getContext()), 0);
                    Value* cnt_val = ConstantInt::get(Type::getInt32Ty(whole_module->getContext()), cnt);
                    Value *IndexList[] = {zero, cnt_val};
                    ArrayRef<unsigned int> a(cnt);
                    Instruction* gep1 = GetElementPtrInst::CreateInBounds(pt->getElementType(),bitcast_inst,IndexList,"",store_inst);
                    Instruction* ex1 = ExtractValueInst::Create(arg,a,"",store_inst);
                    Instruction* store1 = new StoreInst(ex1,gep1,false,store_inst);
                    cnt++;
                  }
                }
                functions_to_change[f]=literal_struct;
                to_delete.insert(store_inst);
              }
            }
          }
        }
      }
    }

    for (auto inst : to_delete)
    {
      inst->eraseFromParent();
    }

    std::unordered_map<Function*,StructType*> new_functions_for_coercing;

    for (auto k : functions_to_change)
    {
      Function* F = k.first;
      SmallVector<ReturnInst*, 8> Returns;
      std::vector<Type*> new_params;
      for (auto AI = F->arg_begin(), AE = F->arg_end(); AI != AE; ++AI) 
      {
        new_params.push_back(AI->getType());
      }
      auto ft = FunctionType::get(F->getReturnType(),new_params,F->getFunctionType()->isVarArg());
      auto test_function = Function::Create(ft, F->getLinkage(), 200, "", &M);
      test_function->copyAttributesFrom(F);
      Function::arg_iterator DestI = test_function->arg_begin();
      ValueToValueMapTy VMap;
      for (Function::const_arg_iterator J = F->arg_begin(); J != F->arg_end();J++) 
      {
        DestI->setName(J->getName());
        VMap[J] = DestI++;
      }
      auto name = F->getName().str();
      F->setName("");
      CloneFunctionInto(test_function, F, VMap, CloneFunctionChangeType::GlobalChanges, Returns);
      ReplaceUnsafe(F,test_function);
      test_function->setName(name); // This will break for constant initialized by the original function, but eh
      new_functions_for_coercing[test_function]=k.second;
    }

    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto call_inst = dyn_cast<CallInst>(&I))
          {
            Function* f = call_inst->getCalledFunction();
            if (f && new_functions_for_coercing.find(f)!=new_functions_for_coercing.end())
            {
              // There should be one parameter where type doesnt match
              for (int i=0;i<call_inst->arg_size();i++)
              {
                if (f->getArg(i)->getType()!=call_inst->getArgOperand(i)->getType())
                {
                  if (auto load_inst = dyn_cast<LoadInst>(call_inst->getArgOperand(i)))
                  {
                    if (auto bitcast_inst = dyn_cast<BitCastInst>(load_inst->getOperand(0)))
                    {
                      PointerType* pt = PointerType::get(new_functions_for_coercing[f],200);
                      bitcast_inst->mutateType(pt);
                      load_inst->mutateType(new_functions_for_coercing[f]);
                      call_inst->getArgOperand(i)->mutateType(new_functions_for_coercing[f]);
                      auto func_type = call_inst->getCalledFunction()->getFunctionType();
                      call_inst->mutateFunctionType(func_type);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    for (auto k : functions_to_change)
    {
      k.first->eraseFromParent();  
    }

    // Check if we are reuturining coarced value
    std::unordered_set<Function*> functions_with_changed_return_types;
    std::unordered_set<Instruction*> delete_coarced_1;
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto ret_inst = dyn_cast<ReturnInst>(&I))
          {
            if (ret_inst->getNumOperands()>0)
            {
              Value* op = ret_inst->getOperand(0);
              std::string needle = "coerce.val.pi";
              auto name = op->getName().str();
              if (name.find(needle)==0)
              {
                if (auto call_inst = dyn_cast<CallInst>(op))
                {
                  if (call_inst->getCalledFunction()->getName() == "llvm.cheri.cap.address.get.i64")
                  {
                    if (auto bitcast_inst = dyn_cast<BitCastInst>(call_inst->getArgOperand(0)))
                    {
                      ret_inst->setOperand(0,bitcast_inst);
                      functions_with_changed_return_types.insert(&F);
                      delete_coarced_1.insert(call_inst);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    for (auto& f : delete_coarced_1)
    {
      f->eraseFromParent();
    }

    std::unordered_set<Function*> new_functions_coerced2;

    for (auto F : functions_with_changed_return_types)
    {
      SmallVector<ReturnInst*, 8> Returns;
      std::vector<Type*> new_params;
      for (auto AI = F->arg_begin(), AE = F->arg_end(); AI != AE; ++AI) 
      {
        new_params.push_back(AI->getType());
      }
      auto i8_type = Type::getInt8Ty(M.getContext());
      auto ret_pt = PointerType::get(i8_type,200);
      auto ft = FunctionType::get(ret_pt,new_params,F->getFunctionType()->isVarArg());
      auto test_function = Function::Create(ft, F->getLinkage(), 200, "", &M);
      test_function->copyAttributesFrom(F);
      Function::arg_iterator DestI = test_function->arg_begin();
      ValueToValueMapTy VMap;
      for (Function::const_arg_iterator J = F->arg_begin(); J != F->arg_end();J++) 
      {
        DestI->setName(J->getName());
        VMap[J] = DestI++;
      }
      auto name = F->getName().str();
      F->setName("");
      CloneFunctionInto(test_function, F, VMap, CloneFunctionChangeType::GlobalChanges, Returns);
      ReplaceUnsafe(F,test_function);
      test_function->setName(name); // This will break for constant initialized by the original function, but eh
      new_functions_coerced2.insert(test_function);
    }

    for (auto F : functions_with_changed_return_types)
    {
      F->eraseFromParent();  
    }

    std::unordered_set<Value*> calls_of_changed_instructions;
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto call_inst = dyn_cast<CallInst>(&I))
          {
            Function* f = call_inst->getCalledFunction();
            if (f && new_functions_coerced2.find(f)!=new_functions_coerced2.end())
            {
              auto func_type = call_inst->getCalledFunction()->getFunctionType();
              call_inst->mutateFunctionType(func_type);
              calls_of_changed_instructions.insert(&I);
            }
          }
        }
      }
    }

    std::unordered_map<Value*,Value*> call_instruction_mapper;
    std::unordered_set<Instruction*> to_delete_coerced2;

    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto gep_inst = dyn_cast<GetElementPtrInst>(&I))
          {
            auto op_2 = gep_inst->getOperand(1);
            if (op_2 && calls_of_changed_instructions.find(op_2)!=calls_of_changed_instructions.end())
            {
              auto name = gep_inst->getName().str();
              gep_inst->setName("");
              BitCastInst* bt_inst = new BitCastInst(op_2,gep_inst->getType(),name,gep_inst);
              call_instruction_mapper[gep_inst]=bt_inst;
              to_delete_coerced2.insert(gep_inst);
            }
          }
        }
      }
    }

    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          for (int i=0;i<I.getNumOperands();i++)
          {
            auto op = I.getOperand(i);
            if (call_instruction_mapper.find(op)!=call_instruction_mapper.end())
            {
              I.setOperand(i,call_instruction_mapper[op]);
            }
          }
        }
      }
    }

    for (auto k : to_delete_coerced2)
    {
      k->eraseFromParent();
    }

    // Fix the problems with llvm.lifetime instructions
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto call_inst = dyn_cast<CallInst>(&I))
          {
            Function* f = call_inst->getCalledFunction();
            std::string name = "";
            if (f) name = f->getName().str();
            if (is_prefix(name,"llvm.lifetime") && call_inst->getArgOperand(1)->getType()->isPointerTy())
            {
              Instruction* op_inst = dyn_cast<Instruction>(call_inst->getArgOperand(1));
              if (op_inst && op_inst->getOpcode() == Instruction::BitCast)
              {
                auto op0 = op_inst->getOperand(0);
                auto point_type = ((PointerType*)op0->getType())->getElementType();
                int with_cheri = get_size(point_type, true);
                int without_cheri = get_size(point_type, false);
                if (with_cheri!=without_cheri) // if the sizes are different
                {
                  auto val = call_inst->getArgOperand(0);
                  bool do_anything = true;
                  // If it is already an add which simbolizes sizeof(), do not to anything
                  if (auto ins = dyn_cast<Instruction>(val))
                  {
                    if (ins->getOpcode() == Instruction::Add)
                    {
                      if (auto md = ins->getMetadata("sizeof"))
                      {
                        do_anything = false;
                      }
                    }
                  }
                  if (do_anything)
                  {
                    // Has to be immarg
                    ConstantInt* constInt = dyn_cast<ConstantInt>(val);
                    if (constInt)
                    {
                      auto k = constInt->getValue();
                      k*=with_cheri;
                      k=k.sdiv(without_cheri);
                      ConstantInt* new_const_int = ConstantInt::get(M.getContext(), k);
                      call_inst->setArgOperand(0,new_const_int);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    
    //M.dump();
    
    std::unordered_map<Function*,std::unordered_map<std::string,Value*>> things_to_change;
    std::unordered_map<Value*,std::vector<Instruction*>> val_to_bitcast;
    // Fix va_copy
    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto call_inst = dyn_cast<CallInst>(&I))
          {
            auto called_function = call_inst->getCalledFunction();
            if (called_function)
            {
              auto fun_name = called_function->getName().str();
              if (is_prefix(fun_name,"llvm.va_copy."))
              {
                auto source_operand = call_inst->getOperand(1);
                if (auto bitcast_inst = dyn_cast<BitCastInst>(source_operand))
                {
                  // find its .addr
                  if (bitcast_inst->getType() == bitcast_inst->getOperand(0)->getType())
                  {
                    auto new_string = bitcast_inst->getOperand(0)->getName().str()+".addr";
                    things_to_change[&F][new_string]=bitcast_inst->getOperand(0);
                    val_to_bitcast[bitcast_inst->getOperand(0)].push_back(bitcast_inst);
                  }
                }
                auto dest_operand = call_inst->getOperand(0);
                if (auto bitcast_inst = dyn_cast<BitCastInst>(dest_operand))
                {
                  // find its .addr
                  if (bitcast_inst->getType() == bitcast_inst->getOperand(0)->getType())
                  {
                    auto new_string = bitcast_inst->getOperand(0)->getName().str()+".addr";
                    things_to_change[&F][new_string]=bitcast_inst->getOperand(0);
                    val_to_bitcast[bitcast_inst->getOperand(0)].push_back(bitcast_inst);
                  }
                }
              }
              if (is_prefix(fun_name,"llvm.va_start."))
              {
                auto source_operand = call_inst->getOperand(0);
                if (auto bitcast_inst = dyn_cast<BitCastInst>(source_operand))
                {
                  // find its .addr
                  if (bitcast_inst->getType() == bitcast_inst->getOperand(0)->getType())
                  {
                    auto new_string = bitcast_inst->getOperand(0)->getName().str()+".addr";
                    things_to_change[&F][new_string]=bitcast_inst->getOperand(0);
                    val_to_bitcast[bitcast_inst->getOperand(0)].push_back(bitcast_inst);
                  }
                }
              }
              if (is_prefix(fun_name,"llvm.va_end."))
              {
                auto source_operand = call_inst->getOperand(0);
                if (auto bitcast_inst = dyn_cast<BitCastInst>(source_operand))
                {
                  // find its .addr
                  if (bitcast_inst->getType() == bitcast_inst->getOperand(0)->getType())
                  {
                    auto new_string = bitcast_inst->getOperand(0)->getName().str()+".addr";
                    things_to_change[&F][new_string]=bitcast_inst->getOperand(0);
                    val_to_bitcast[bitcast_inst->getOperand(0)].push_back(bitcast_inst);
                  }
                }
              }
            }
          }
        }
      }
    }

    for (auto& F : M)
    {
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (things_to_change.find(&F)!=things_to_change.end())
          {
            if (things_to_change[&F].find(I.getName().str())!=things_to_change[&F].end())
            {
              auto bitcasts = val_to_bitcast[things_to_change[&F][I.getName().str()]];
              for (auto bitcast : bitcasts)
              {
                bitcast->setOperand(0,&I);
              }
            }
          }
        }
      }
    }

    // Fixing for malloc - veeeery specific
    std::vector<Instruction*> mask_insts;
    std::vector<Value*> starters_for_mask_insts;
    std::vector<Instruction*> maloc_insts;
    std::vector<Instruction*> sub_insts;
    std::vector<Instruction*> ptraddr_insts;
    std::vector<Instruction*> load_insts;
    bool fixing_for_malloc = false;
    Instruction* prev_inst = nullptr;
    for (auto& F : M)
    {
      if (F.getName()!="malloc") continue;
      for (auto& B : F)
      {
        for (auto& I : B)
        {
          if (auto md = I.getMetadata("malloc_builtup"))
          {
            if (prev_inst)
            {
              mask_insts.push_back(prev_inst);
              starters_for_mask_insts.push_back(I.getOperand(0));
              maloc_insts.push_back(&I);
              fixing_for_malloc = true;
            }
          }
          prev_inst=&I;
        }
      }
    }

    if (fixing_for_malloc)
    {
      // heap has to be called - heap! - can be fixed with annotation
      GlobalVariable* gv_heap = nullptr;
      for (GlobalVariable& GV : M.globals()) 
      {
        if (GV.getName() == "heap") 
        {
          gv_heap = &GV;
        }
      }

      if (gv_heap)
      {      
        for (int i=0;i<mask_insts.size();i++)
        {
          Instruction* mask_inst = mask_insts[i];
          Instruction* malloc_inst = maloc_insts[i];
          Value* op = starters_for_mask_insts[i];
          auto id = Function::lookupIntrinsicID("llvm.cheri.representable.alignment.mask.i64");
          auto i64_type = Type::getInt64Ty(M.getContext());
          std::vector<Type*> over_types;
          over_types.push_back(i64_type);
          auto instrisic_function = Intrinsic::getDeclaration(&M,id,ArrayRef<Type*>(over_types));
          std::vector<Value*> arguments;
          arguments.push_back(op);
          ArrayRef<Value*> args(arguments);
          auto name = mask_inst->getName().str();
          CallInst* call_inst = CallInst::Create(instrisic_function->getFunctionType(),instrisic_function,args,"",mask_inst);
          ConstantInt *Zero = ConstantInt::getSigned(i64_type, 0);
          Instruction *Sub = BinaryOperator::CreateSub(Zero, call_inst, "sub", mask_inst);
          sub_insts.push_back(Sub);
          mask_inst->setOperand(0,Sub);

          PointerType* pt = (PointerType*)(gv_heap->getType());
          LoadInst* load_inst = new LoadInst(pt->getElementType(),gv_heap,"",malloc_inst);
          load_insts.push_back(load_inst);

          auto id2 = Function::lookupIntrinsicID("llvm.cheri.cap.address.get.i64");
          std::vector<Type*> over_types2;
          over_types2.push_back(i64_type);
          auto instrisic_function2 = Intrinsic::getDeclaration(&M,id2,ArrayRef<Type*>(over_types2));
          std::vector<Value*> arguments2;
          arguments2.push_back(load_inst);
          ArrayRef<Value*> args2(arguments2);
          auto name2 = "ptraddr";
          CallInst* call_inst2 = CallInst::Create(instrisic_function2->getFunctionType(),instrisic_function2,args2,"",malloc_inst);
          ptraddr_insts.push_back(call_inst2);
          malloc_inst->setOperand(0,call_inst2);
        }
      }


      std::vector<Instruction*> maloc_reses;
      std::vector<Instruction*> next_insts;
      prev_inst=nullptr;
      for (auto& F : M)
      {
        if (F.getName()!="malloc") continue;
        for (auto& B : F)
        {
          for (auto& I : B)
          {
            if (auto md = I.getMetadata("malloc_result"))
            {
              maloc_reses.push_back(&I);
              next_insts.push_back(I.getNextNode());
            }
          }
        }
      }

      Instruction* new_ptr;
      Value* size_addr;

      for (int i=0;i<maloc_reses.size();i++)
      {
        auto maloc_res = maloc_reses[i];
        auto next_inst = next_insts[i];
        maloc_res->setName("aligned_intptr");
        Instruction* sub = BinaryOperator::CreateSub(maloc_res, ptraddr_insts[i], "", next_inst);
        auto i8_type = Type::getInt8Ty(M.getContext());
        GetElementPtrInst* gepInst = GetElementPtrInst::Create(i8_type, load_insts[i], sub, "aligned_result",next_inst);
        auto id = Function::lookupIntrinsicID("llvm.assume");
        std::vector<Type*> over_types;
        Type *boolType = Type::getInt1Ty(M.getContext());
        over_types.push_back(boolType);
        auto instrisic_function = Intrinsic::getDeclaration(&M,id);
        auto const_true = ConstantInt::getTrue(M.getContext());
        std::vector<Value*> arguments;
        arguments.push_back(const_true);
        MDBuilder mdBuilder(M.getContext());
        ArrayRef<Value*> args(arguments);
        Metadata *alignOps[] = {ValueAsMetadata::get(gepInst), ValueAsMetadata::get(sub_insts[i])};
        ArrayRef<Metadata *> alignOpsRef(alignOps, 2);
        MDNode *alignMetadata = MDNode::get(M.getContext(), alignOpsRef);
        const char *bundleTag = "align";
        std::vector<Value*> arguments_bundle;
        arguments_bundle.push_back(gepInst);
        arguments_bundle.push_back(sub_insts[i]);
        OperandBundleDef bundleDef(bundleTag, arguments_bundle);
        std::vector<OperandBundleDef> opbfd;
        opbfd.push_back(bundleDef);
        ArrayRef<OperandBundleDef> ar_obdf(opbfd);
        CallInst* call_inst = CallInst::Create(instrisic_function->getFunctionType(),instrisic_function,args, ar_obdf, "", next_inst);
        // Make new_ptr
        PointerType* pt = PointerType::get(i8_type,200);
        AllocaInst* alloca_inst = new AllocaInst(pt,200,"new_ptr", next_inst);
        new_ptr = alloca_inst;
        StoreInst* store_inst = new StoreInst(gepInst,alloca_inst,false,Align(16),next_inst);
        size_addr = ((Instruction*)starters_for_mask_insts[i])->getOperand(0);
        auto i64_type = Type::getInt64Ty(M.getContext());
        LoadInst* load_inst = new LoadInst(i64_type, size_addr, "",next_inst);
        ConstantInt *num_15 = ConstantInt::getSigned(i64_type, 15);
        ConstantInt *num_minus_16 = ConstantInt::getSigned(i64_type, -16);
        Instruction* add1 = BinaryOperator::CreateAdd(load_inst, num_15, "over_boundary", next_inst);
        Instruction* add2 = BinaryOperator::CreateAdd(add1, num_minus_16, "aligned_result", next_inst);
        Instruction* next_next_inst = next_inst->getNextNode();
        next_inst->setOperand(0,add2);
        next_next_inst->setOperand(0,alloca_inst);
      }


      // Lastly, fix retval
      Instruction* last_ret_instruction;
      for (auto& F : M)
      {
        if (F.getName()!="malloc") continue;
        for (auto& B : F)
        {
          for (auto& I : B)
          {
            if (auto store_inst = dyn_cast<StoreInst>(&I))
            {
              Value* op_store = store_inst->getOperand(1);
              if (op_store->getName().str()=="retval")
              {
                last_ret_instruction=&I;
              }
            }
          }
        }
      }

      if (last_ret_instruction)
      {
        BasicBlock* bb = last_ret_instruction->getParent();
        for (auto& I : *bb)
        {
          if (auto load_inst = dyn_cast<LoadInst>(&I))
          {
            Value* op = I.getOperand(0);
            if (op==gv_heap)
            {
              I.setOperand(0,new_ptr);
            }
          } 
        }
        LoadInst* load_inst = new LoadInst(((PointerType*)size_addr->getType())->getElementType(),size_addr,"",last_ret_instruction);
        auto id2 = Function::lookupIntrinsicID("llvm.cheri.round.representable.length.i64");
        auto i64_type = Type::getInt64Ty(M.getContext());
        std::vector<Type*> over_types2;
        over_types2.push_back(i64_type);
        auto instrisic_function2 = Intrinsic::getDeclaration(&M,id2,ArrayRef<Type*>(over_types2));
        std::vector<Value*> arguments2;
        arguments2.push_back(load_inst);
        ArrayRef<Value*> args2(arguments2);
        CallInst* call_inst2 = CallInst::Create(instrisic_function2->getFunctionType(),instrisic_function2,args2,"",last_ret_instruction);
        AllocaInst* bounds_alloca = new AllocaInst(i64_type,200,"bounds",last_ret_instruction);
        StoreInst* store_inst = new StoreInst(call_inst2,bounds_alloca,last_ret_instruction);
        LoadInst* load_inst2 = new LoadInst(((PointerType*)new_ptr->getType())->getElementType(),new_ptr,"",last_ret_instruction);
        LoadInst* load_inst3 = new LoadInst(((PointerType*)bounds_alloca->getType())->getElementType(),bounds_alloca,"",last_ret_instruction);
        auto id3 = Function::lookupIntrinsicID("llvm.cheri.cap.bounds.set.exact.i64");
        std::vector<Type*> over_types3;
        over_types3.push_back(load_inst3->getType());
        auto instrisic_function3 = Intrinsic::getDeclaration(&M,id3,ArrayRef<Type*>(over_types3));
        std::vector<Value*> arguments3;
        arguments3.push_back(load_inst2);
        arguments3.push_back(load_inst3);
        ArrayRef<Value*> args3(arguments3);
        CallInst* call_inst3 = CallInst::Create(instrisic_function3->getFunctionType(),instrisic_function3,args3,"",last_ret_instruction);
        last_ret_instruction->setOperand(0,call_inst3);
      }
    }

    return true;
  }

}; // end of struct Hello
}  // end of anonymous namespace

// LAST WORKING THING BEFORE CHANGING LLVM!

char Hello::ID = 0;
static RegisterPass<Hello> X("hello", "Hello World Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);