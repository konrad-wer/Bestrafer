#include "Bestrafer.h"
#include "BuiltinFunctions.h"

namespace Bestrafer {

StoreValue Unit = StoreValue {unit::u};

StoreValue Bool(const bool& b) {
  StoreValue v;
  v.val = b;
  return v;
}

StoreValue Int(const int64_t& n) {
  StoreValue v;
  v.val = n;
  return v;
}

StoreValue Float(const long double& x) {
  StoreValue v;
  v.val = x;
  return v;
}

StoreValue Char(const char& c) {
  StoreValue v;
  v.val = c;
  return v;
}

StoreValue String(const std::string& s) {
  StoreValue v;
  v.val = s;
  return v;
}

StoreValue MakeRef(const std::shared_ptr<HeapValue>& ref) {
  StoreValue v;
  v.val = ref;
  return v;
}

StoreValue FromSelf(const std::weak_ptr<HeapValue>& ref) {
  StoreValue v;
  v.val = ref.lock();
  return v;
}

bool Tuple::IsEqual(const HeapValue& v) {
  const auto& v_elems = ((Tuple&)v).elems;

  for (int i = 0; i < elems.size(); i++)
    if (!std::get<bool>(op_eq(elems[i], v_elems[i]).val))
      return false;

  return true;
}

bool Tuple::IsLess(const HeapValue& v) {
  const auto& v_elems = ((Tuple&)v).elems;

  for (int i = 0; i < elems.size(); i++) {
    if (std::get<bool>(op_ls(elems[i], v_elems[i]).val))
      return true;
    if (std::get<bool>(op_gt(elems[i], v_elems[i]).val))
      return false;
  }

  return false;
}

bool Tuple::IsLessOrEqual(const HeapValue& v) {
  const auto& v_elems = ((Tuple&)v).elems;

  for (int i = 0; i < elems.size(); i++) {
    if (std::get<bool>(op_ls(elems[i], v_elems[i]).val))
      return true;
    if (std::get<bool>(op_gt(elems[i], v_elems[i]).val))
      return false;
  }

  return true;
}

bool Constr::IsEqual(const HeapValue& v) {
  return (constr_name == ((Constr&)v).constr_name) && Tuple::IsEqual(v);
}

bool Constr::IsLess(const HeapValue& v) {
  const auto& v_constr_name = ((Constr&)v).constr_name;

  if (constr_name < v_constr_name)
    return true;
  if (constr_name > v_constr_name)
    return false;

  return Tuple::IsLess(v);
}

bool Constr::IsLessOrEqual(const HeapValue& v) {
  const auto& v_constr_name = ((Constr&)v).constr_name;

  if (constr_name < v_constr_name)
    return true;
  if (constr_name > v_constr_name)
    return false;

  return Tuple::IsLessOrEqual(v);
}

} // namespace Bestrafer
