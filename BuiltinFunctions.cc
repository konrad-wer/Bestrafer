#include "BuiltinFunctions.h"

namespace Bestrafer {

StoreValue s_readFile = MakeRef(std::make_shared<cl_s_readFile>());
StoreValue s_writeFile =MakeRef(std::make_shared<cl_s_writeFile<false>>());
StoreValue s_appendFile =MakeRef(std::make_shared<cl_s_writeFile<true>>());
StoreValue s_putChar = MakeRef(std::make_shared<cl_s_print<char, false>>());
StoreValue s_putStr = MakeRef(std::make_shared<cl_s_print<std::string, false>>());
StoreValue s_putStrLn = MakeRef(std::make_shared<cl_s_print<std::string, true>>());
StoreValue s_printBool = MakeRef(std::make_shared<cl_s_print<bool, true>>());
StoreValue s_printInt = MakeRef(std::make_shared<cl_s_print<int64_t, true>>());
StoreValue s_printFloat = MakeRef(std::make_shared<cl_s_print<long double, true>>());
StoreValue s_getChar = MakeRef(std::make_shared<cl_s_getChar>());
StoreValue s_getLine = MakeRef(std::make_shared<cl_s_getLine>());
StoreValue s_readLnBool = MakeRef(std::make_shared<cl_s_readLnBool>());
StoreValue s_readLnInt = MakeRef(std::make_shared<cl_s_readLnInt>());
StoreValue s_readLnFloat = MakeRef(std::make_shared<cl_s_readLnFloat>());

StoreValue s_stringToList = MakeRef(std::make_shared<cl_s_stringToList>());
StoreValue s_stringFromList = MakeRef(std::make_shared<cl_s_stringFromList>());
StoreValue s_intToFloat = MakeRef(std::make_shared<cl_cast<int64_t, long double>>());
StoreValue s_floatToInt = MakeRef(std::make_shared<cl_cast<long double, int64_t>>());
StoreValue s_intToString = MakeRef(std::make_shared<cl_to_string<int64_t>>());
StoreValue s_floatToString = MakeRef(std::make_shared<cl_to_string<long double>>());
StoreValue s_boolToString = MakeRef(std::make_shared<cl_s_boolToString>());
StoreValue s_charToString = MakeRef(std::make_shared<cl_s_charToString>());
StoreValue s_ord = MakeRef(std::make_shared<cl_cast<char, int64_t>>());
StoreValue s_chr = MakeRef(std::make_shared<cl_cast<int64_t, char>>());
StoreValue s_intFromString = MakeRef(std::make_shared<cl_s_intFromString>());
StoreValue s_floatFromString = MakeRef(std::make_shared<cl_s_floatFromString>());


StoreValue op_unary_not(const StoreValue& v) {
  return Bool(!std::get<bool>(v.val));
}

StoreValue op_unary_minus(const StoreValue& v) {
  return Int(-std::get<int64_t>(v.val));
}

StoreValue op_unary_minus_float(const StoreValue& v){
   return Float(-std::get<long double>(v.val));
}

StoreValue op_plus(const StoreValue& v1, const StoreValue& v2) {
  return Int(std::get<int64_t>(v1.val) + std::get<int64_t>(v2.val));
}

StoreValue op_minus(const StoreValue& v1, const StoreValue& v2) {
  return Int(std::get<int64_t>(v1.val) - std::get<int64_t>(v2.val));
}

StoreValue op_mult(const StoreValue& v1, const StoreValue& v2) {
  return Int(std::get<int64_t>(v1.val) * std::get<int64_t>(v2.val));
}

StoreValue op_div(const StoreValue& v1, const StoreValue& v2) {
  int64_t n2 = std::get<int64_t>(v2.val);
  if (n2 == 0)
    throw DivisionByZeroException();
  else
    return Int(std::get<int64_t>(v1.val) / n2);
}

StoreValue op_mod(const StoreValue& v1, const StoreValue& v2) {
  int64_t n2 = std::get<int64_t>(v2.val);
  if (n2 == 0)
    throw DivisionByZeroException();
  else
    return Int(std::get<int64_t>(v1.val) % n2);
}

StoreValue op_plus_float(const StoreValue& v1, const StoreValue& v2) {
  return Float(std::get<long double>(v1.val) + std::get<long double>(v2.val));
}

StoreValue op_minus_float(const StoreValue& v1, const StoreValue& v2) {
  return Float(std::get<long double>(v1.val) - std::get<long double>(v2.val));
}

StoreValue op_mult_float(const StoreValue& v1, const StoreValue& v2) {
  return Float(std::get<long double>(v1.val) * std::get<long double>(v2.val));
}

StoreValue op_div_float(const StoreValue& v1, const StoreValue& v2) {
  return Float(std::get<long double>(v1.val) / std::get<long double>(v2.val));
}

StoreValue op_and(const StoreValue& v1, const StoreValue& v2) {
  return Bool(std::get<bool>(v1.val) && std::get<bool>(v2.val));
}

StoreValue op_or(const StoreValue& v1, const StoreValue& v2) {
  return Bool(std::get<bool>(v1.val) || std::get<bool>(v2.val));
}

StoreValue op_concat(const StoreValue& v1, const StoreValue& v2) {
  return String(std::get<std::string>(v1.val) + std::get<std::string>(v2.val));
}

StoreValue op_compose(const StoreValue& v1, const StoreValue& v2) {
  return MakeRef(std::make_shared<cl_compose>(v1, v2));
}

StoreValue op_append_vec(const StoreValue& v1, const StoreValue& v2) {
  Constr* constr;
  constr = (Constr*)std::get<std::shared_ptr<HeapValue>>(v1.val).get();

  if (constr->GetName() == "[]") {
    return v2;
  }

  auto ptr = std::make_shared<Constr>(":", std::vector<StoreValue>({}));
  StoreValue result = MakeRef(ptr);
  ptr->elems.push_back(constr->elems[0]);
  constr = (Constr*)std::get<std::shared_ptr<HeapValue>>(constr->elems[1].val).get();

  while (constr->GetName() == ":") {
    auto new_ptr = std::make_shared<Constr>(":", std::vector<StoreValue>({}));
    ptr->elems.push_back(MakeRef(new_ptr));
    ptr = new_ptr;
    ptr->elems.push_back(constr->elems[0]);
    constr = (Constr*)std::get<std::shared_ptr<HeapValue>>(constr->elems[1].val).get();
  }
  ptr->elems.push_back(v2);
  return result;
}

StoreValue op_append_list(const StoreValue& v1, const StoreValue& v2) {
  Constr* constr;
  constr = (Constr*)std::get<std::shared_ptr<HeapValue>>(v1.val).get();

  if (constr->GetName() == "{}") {
    return v2;
  }

  auto ptr = std::make_shared<Constr>(";", std::vector<StoreValue>({}));
  StoreValue result = MakeRef(ptr);
  ptr->elems.push_back(constr->elems[0]);
  constr = (Constr*)std::get<std::shared_ptr<HeapValue>>(constr->elems[1].val).get();

  while (constr->GetName() == ";") {
    auto new_ptr = std::make_shared<Constr>(";", std::vector<StoreValue>({}));
    ptr->elems.push_back(MakeRef(new_ptr));
    ptr = new_ptr;
    ptr->elems.push_back(constr->elems[0]);
    constr = (Constr*)std::get<std::shared_ptr<HeapValue>>(constr->elems[1].val).get();
  }
  ptr->elems.push_back(v2);
  return result;
}

StoreValue op_eq(const StoreValue& v1, const StoreValue& v2) {
  if (std::holds_alternative<unit>(v1.val))
    return Bool(true);
  else if (std::holds_alternative<bool>(v1.val))
    return Bool(std::get<bool>(v1.val) == std::get<bool>(v2.val));
  else if (std::holds_alternative<int64_t>(v1.val))
    return Bool(std::get<int64_t>(v1.val) == std::get<int64_t>(v2.val));
  else if (std::holds_alternative<long double>(v1.val))
    return Bool(std::get<long double>(v1.val) == std::get<long double>(v2.val));
  else if (std::holds_alternative<char>(v1.val))
    return Bool(std::get<char>(v1.val) == std::get<char>(v2.val));
  else if (std::holds_alternative<std::string>(v1.val))
    return Bool(std::get<std::string>(v1.val) == std::get<std::string>(v2.val));
  else
    return Bool(std::get<std::shared_ptr<HeapValue>>(v1.val)->IsEqual(*std::get<std::shared_ptr<HeapValue>>(v2.val)));
}

StoreValue op_neq(const StoreValue& v1, const StoreValue& v2)  {
  if (std::holds_alternative<unit>(v1.val))
    return Bool(false);
  else if (std::holds_alternative<bool>(v1.val))
    return Bool(std::get<bool>(v1.val) != std::get<bool>(v2.val));
  else if (std::holds_alternative<int64_t>(v1.val))
    return Bool(std::get<int64_t>(v1.val) != std::get<int64_t>(v2.val));
  else if (std::holds_alternative<long double>(v1.val))
    return Bool(std::get<long double>(v1.val) != std::get<long double>(v2.val));
  else if (std::holds_alternative<char>(v1.val))
    return Bool(std::get<char>(v1.val) != std::get<char>(v2.val));
  else if (std::holds_alternative<std::string>(v1.val))
    return Bool(std::get<std::string>(v1.val) != std::get<std::string>(v2.val));
  else
    return Bool(!std::get<std::shared_ptr<HeapValue>>(v1.val)->IsEqual(*std::get<std::shared_ptr<HeapValue>>(v2.val)));
}

StoreValue op_le(const StoreValue& v1, const StoreValue& v2) {
  if (std::holds_alternative<unit>(v1.val))
    return Bool(true);
  else if (std::holds_alternative<bool>(v1.val))
    return Bool(std::get<bool>(v1.val) <= std::get<bool>(v2.val));
  else if (std::holds_alternative<int64_t>(v1.val))
    return Bool(std::get<int64_t>(v1.val) <= std::get<int64_t>(v2.val));
  else if (std::holds_alternative<long double>(v1.val))
    return Bool(std::get<long double>(v1.val) <= std::get<long double>(v2.val));
  else if (std::holds_alternative<char>(v1.val))
    return Bool(std::get<char>(v1.val) <= std::get<char>(v2.val));
  else if (std::holds_alternative<std::string>(v1.val))
    return Bool(std::get<std::string>(v1.val) <= std::get<std::string>(v2.val));
  else
    return Bool(std::get<std::shared_ptr<HeapValue>>(v1.val)->IsLessOrEqual(*std::get<std::shared_ptr<HeapValue>>(v2.val)));
}

StoreValue op_ge(const StoreValue& v1, const StoreValue& v2) {
  if (std::holds_alternative<unit>(v1.val))
    return Bool(true);
  else if (std::holds_alternative<bool>(v1.val))
    return Bool(std::get<bool>(v1.val) >= std::get<bool>(v2.val));
  else if (std::holds_alternative<int64_t>(v1.val))
    return Bool(std::get<int64_t>(v1.val) >= std::get<int64_t>(v2.val));
  else if (std::holds_alternative<long double>(v1.val))
    return Bool(std::get<long double>(v1.val) >= std::get<long double>(v2.val));
  else if (std::holds_alternative<char>(v1.val))
    return Bool(std::get<char>(v1.val) >= std::get<char>(v2.val));
  else if (std::holds_alternative<std::string>(v1.val))
    return Bool(std::get<std::string>(v1.val) >= std::get<std::string>(v2.val));
  else
    return Bool(std::get<std::shared_ptr<HeapValue>>(v2.val)->IsLessOrEqual(*std::get<std::shared_ptr<HeapValue>>(v1.val)));
}

StoreValue op_ls(const StoreValue& v1, const StoreValue& v2) {
  if (std::holds_alternative<unit>(v1.val))
    return Bool(false);
  else if (std::holds_alternative<bool>(v1.val))
    return Bool(std::get<bool>(v1.val) < std::get<bool>(v2.val));
  else if (std::holds_alternative<int64_t>(v1.val))
    return Bool(std::get<int64_t>(v1.val) < std::get<int64_t>(v2.val));
  else if (std::holds_alternative<long double>(v1.val))
    return Bool(std::get<long double>(v1.val) < std::get<long double>(v2.val));
  else if (std::holds_alternative<char>(v1.val))
    return Bool(std::get<char>(v1.val) < std::get<char>(v2.val));
  else if (std::holds_alternative<std::string>(v1.val))
    return Bool(std::get<std::string>(v1.val) < std::get<std::string>(v2.val));
  else
    return Bool(std::get<std::shared_ptr<HeapValue>>(v1.val)->IsLess(*std::get<std::shared_ptr<HeapValue>>(v2.val)));
}

StoreValue op_gt(const StoreValue& v1, const StoreValue& v2) {
  if (std::holds_alternative<unit>(v1.val))
    return Bool(false);
  else if (std::holds_alternative<bool>(v1.val))
    return Bool(std::get<bool>(v1.val) > std::get<bool>(v2.val));
  else if (std::holds_alternative<int64_t>(v1.val))
    return Bool(std::get<int64_t>(v1.val) > std::get<int64_t>(v2.val));
  else if (std::holds_alternative<long double>(v1.val))
    return Bool(std::get<long double>(v1.val) > std::get<long double>(v2.val));
  else if (std::holds_alternative<char>(v1.val))
    return Bool(std::get<char>(v1.val) > std::get<char>(v2.val));
  else if (std::holds_alternative<std::string>(v1.val))
    return Bool(std::get<std::string>(v1.val) > std::get<std::string>(v2.val));
  else
    return Bool(std::get<std::shared_ptr<HeapValue>>(v2.val)->IsLess(*std::get<std::shared_ptr<HeapValue>>(v1.val)));
}

} // namespace Bestrafer
