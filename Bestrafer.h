#ifndef BESTRAFER_H_
#define BESTRAFER_H_

#include <memory>
#include <variant>
#include <vector>
#include <iostream>

namespace Bestrafer {

struct HeapValue {
  virtual bool IsEqual(const HeapValue& v) = 0;
  virtual bool IsLess(const HeapValue& v) = 0;
  virtual bool IsLessOrEqual(const HeapValue& v) = 0;
};

enum class unit {u};

struct StoreValue {
  std::variant<unit, bool, int64_t, long double, char, std::string, std::shared_ptr<HeapValue>> val;
};

extern StoreValue Unit;
StoreValue Bool(const bool& b);
StoreValue Int(const int64_t& n);
StoreValue Float(const long double& x);
StoreValue Char(const char& c);
StoreValue String(const std::string& s);
StoreValue MakeRef(const std::shared_ptr<HeapValue>& ref);
StoreValue FromSelf(const std::weak_ptr<HeapValue>& ref);

struct Closure : public HeapValue {
  virtual StoreValue Call(const StoreValue& arg) = 0;
  virtual StoreValue CallNoCopy(const StoreValue& arg) = 0;

  bool IsEqual(const HeapValue& v) override { return false; };
  bool IsLess(const HeapValue& v) override { return false; };
  bool IsLessOrEqual(const HeapValue& v) override { return false; };

  Closure() {}
  explicit Closure(std::vector<StoreValue> refs) : refs(std::move(refs)) {}

  std::vector<StoreValue> refs;
  std::weak_ptr<HeapValue> self;
};

struct Tuple : public HeapValue {

  Tuple(std::vector<StoreValue> es) : elems(std::move(es)) {}

  StoreValue GetElem(int n) { return elems[n]; }
  bool IsEqual(const HeapValue& v) override;
  bool IsLess(const HeapValue& v) override;
  bool IsLessOrEqual(const HeapValue& v) override;

  std::vector<StoreValue> elems;
};

struct Constr : public Tuple {

  Constr(std::string name, std::vector<StoreValue> es) :
    Tuple(std::move(es)), constr_name(std::move(name)) {}

  std::string GetName() { return constr_name; }

  std::string constr_name;
  bool IsEqual(const HeapValue& v) override;
  bool IsLess(const HeapValue& v) override;
  bool IsLessOrEqual(const HeapValue& v) override;
};

class RuntimeException: public std::exception
{
 public:
  RuntimeException (StoreValue v) : message_ (std::get<std::string>(v.val)) {}

  virtual const char* what() const throw()
  {
    return message_.c_str();
  }

 private:
  std::string message_;
};

class ArithmeticException : public std::exception
{
  virtual const char* what() const throw()
  {
    return "Arithmetic exception";
  }
};

class DivisionByZeroException : public ArithmeticException
{
  virtual const char* what() const throw()
  {
    return "Division by zero exception";
  }
};

} // namespace Bestrafer

#endif
