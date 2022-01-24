#ifndef BUILITNFUNCTIONS_H_
#define BUILITNFUNCTIONS_H_

#include "Bestrafer.h"
#include <iostream>
#include <fstream>

namespace Bestrafer {

namespace {
  int64_t safe_stoll(std::string s) {
    if (s.find('.') != std::string::npos)
      throw std::runtime_error("ProbablyFloat");
    if (s.find('e') != std::string::npos)
      throw std::runtime_error("ProbablyFloat");
    return std::stoll(s);
  }

  void trim(std::string& str)
  {
    str.erase(0, str.find_first_not_of("\t\n\v\f\r "));
    str.erase(str.find_last_not_of("\t\n\v\f\r ") + 1);
  }

} // namespace

template <bool Append>
struct cl_s_writeFile2 : public Closure {
  StoreValue Call(const StoreValue& v) override {
    return CallNoCopy(v);
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    std::string filename = std::get<std::string>(refs[0].val);
    std::string contents = std::get<std::string>(v.val);

    std::ofstream fout;
    if constexpr (Append)
       fout.open(filename, std::ios::app);
    else
      fout.open(filename);

    if (fout.fail())
      throw std::ios_base::failure("Failed when trying to open a file '" + filename + "'");

    fout << contents;

    fout.close();
    return Unit;
  }
};

template <bool Append>
struct cl_s_writeFile : public Closure {
  StoreValue Call(const StoreValue& v) override {
    auto closure_ptr = std::make_shared<cl_s_writeFile2<Append>>();

    closure_ptr->refs.push_back(v);
    return MakeRef(closure_ptr);
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_readFile : public Closure {
  StoreValue Call(const StoreValue& v) override {
    auto filename = std::get<std::string>(v.val);
    std::ifstream fin;
    fin.open(filename);
    std::string res;
    char c;

    if (fin.fail())
      throw std::ios_base::failure("Failed when trying to open a file '" + filename + "'");

    while (fin.get(c))
      res += c;

    fin.close();
    return String(res);
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

template <typename T, bool NewLine>
struct cl_s_print : public Closure {
  StoreValue Call(const StoreValue& v) override {
    std::cout << std::get<T>(v.val);
    if constexpr (NewLine)
      std::cout << std::endl;
    return v;
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

template <>
struct cl_s_print <bool, true> : public Closure {
  StoreValue Call(const StoreValue& v) override {
    if (std::get<bool>(v.val))
      std::cout << "True\n";
    else
      std::cout << "False\n";
    return v;
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_getChar : public Closure {
  StoreValue Call(const StoreValue& v) override {
    int c = std::getchar();
    if (c != EOF)
      return Char((char)c);
    else
      throw std::ios_base::failure("Could not read a character from stdin");
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_getLine : public Closure {
  StoreValue Call(const StoreValue& v) override {
    std::string s;
    std::getline(std::cin, s);
    return String(s);
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_readLnBool : public Closure {
  StoreValue Call(const StoreValue& v) override {
    std::string s;
    std::getline(std::cin, s);
    trim(s);
    if(s == "True") return Bool(true);
    if(s == "False") return Bool(false);
    throw std::ios_base::failure("Could not convert input string to a bool");
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_readLnInt : public Closure {
  StoreValue Call(const StoreValue& v) override {
    std::string s;
    std::getline(std::cin, s);
    try {
      int64_t res;
      res = safe_stoll(s);
      return Int(res);
    } catch (...) {
      throw std::ios_base::failure("Could not convert input string to an int");
    }
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_readLnFloat : public Closure {
  StoreValue Call(const StoreValue& v) override {
    std::string s;
    std::getline(std::cin, s);
    try {
      long double res;
      res = std::stold(s);
      return Float(res);
    } catch (...) {
      throw std::ios_base::failure("Could not convert input string to a float");
    }
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

extern StoreValue s_readFile;
extern StoreValue s_writeFile;
extern StoreValue s_appendFile;
extern StoreValue s_putChar;
extern StoreValue s_putStr;
extern StoreValue s_putStrLn;
extern StoreValue s_printBool;
extern StoreValue s_printInt;
extern StoreValue s_printFloat;
extern StoreValue s_getChar;
extern StoreValue s_getLine;
extern StoreValue s_readLnBool;
extern StoreValue s_readLnInt;
extern StoreValue s_readLnFloat;

template <typename T>
struct cl_to_string : public Closure {
  StoreValue Call(const StoreValue& v) override {
    return String(std::to_string(std::get<T>(v.val)));
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

template <typename Tfrom, typename Tto>
struct cl_cast : public Closure {
  StoreValue Call(const StoreValue& v) override {
    StoreValue v2;
    v2.val = (Tto)std::get<Tfrom>(v.val);
    return v2;
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_boolToString : public Closure {
  StoreValue Call(const StoreValue& v) override {
    if (std::get<bool>(v.val)) {
      return String("True");
    } else {
      return String("False");
    }
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};


struct cl_s_charToString : public Closure {
  StoreValue Call(const StoreValue& v) override {
    StoreValue v2;
    std::string s = "";
    s += std::get<char>(v.val);
    v2.val = s;
    return v2;
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_intFromString : public Closure {
  StoreValue Call(const StoreValue& v) override {
    try {
      int64_t res;
      std::string s = std::get<std::string>(v.val);
      res = safe_stoll(s);
      return Int(res);
    } catch (...) {
      throw RuntimeException(String("intFromString: given string is not an int"));
    }
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_floatFromString : public Closure {
  StoreValue Call(const StoreValue& v) override {
    try {
      long double res;
      std::string s = std::get<std::string>(v.val);
      res = std::stold(s);
      return Float(res);
    } catch (...) {
      throw RuntimeException(String("floatFromString: given string is not a float"));
    }
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};


struct cl_s_stringFromList : public Closure {
  StoreValue Call(const StoreValue& v) override {
    std::string  res = "";
    Constr* constr = (Constr*)std::get<std::shared_ptr<HeapValue>>(v.val).get();

    while (constr->GetName() != "{}") {
      res += std::get<char>(constr->GetElem(0).val);
      constr = (Constr*)std::get<std::shared_ptr<HeapValue>>(constr->GetElem(1).val).get();
    }

    return String(res);
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

struct cl_s_stringToList : public Closure {
  StoreValue Call(const StoreValue& v) override {
    std::string s = std::get<std::string>(v.val);

    if (s == "")
      return MakeRef(std::make_shared<Constr>("{}", std::vector<StoreValue>({})));

    auto ptr = std::make_shared<Constr>(";", std::vector<StoreValue>({}));
    StoreValue result = MakeRef(ptr);
    ptr->elems.push_back(Char(s[0]));

    for (int i = 1; i < s.length(); i++) {
      auto new_ptr = std::make_shared<Constr>(";", std::vector<StoreValue>({}));
      ptr->elems.push_back(MakeRef(new_ptr));
      ptr = new_ptr;
      ptr->elems.push_back(Char(s[i]));
    }
    ptr->elems.push_back(MakeRef(std::make_shared<Constr>("{}", std::vector<StoreValue>({}))));
    return result;
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    return Call(v);
  }
};

extern StoreValue s_stringToList;
extern StoreValue s_stringFromList;
extern StoreValue s_intToFloat;
extern StoreValue s_floatToInt;
extern StoreValue s_intToString;
extern StoreValue s_floatToString;
extern StoreValue s_boolToString;
extern StoreValue s_charToString;
extern StoreValue s_ord;
extern StoreValue s_chr;
extern StoreValue s_intFromString;
extern StoreValue s_floatFromString;

extern StoreValue op_unary_not(const StoreValue& v);
extern StoreValue op_unary_minus(const StoreValue& v);
extern StoreValue op_unary_minus_float(const StoreValue& v);
extern StoreValue op_plus(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_minus(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_mult(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_div(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_mod(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_plus_float(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_minus_float(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_mult_float(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_div_float(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_and(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_or(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_concat(const StoreValue& v1, const StoreValue& v2);

struct cl_compose : public Closure {
  cl_compose(StoreValue f, StoreValue g) :
    f_(std::get<std::shared_ptr<HeapValue>>(f.val)),
    g_(std::get<std::shared_ptr<HeapValue>>(g.val))
  {}

  StoreValue Call(const StoreValue& v) override {
    StoreValue v2 = ((Closure*)g_.get())->Call(v);
    return ((Closure*)f_.get())->Call(v2);
  }

  StoreValue CallNoCopy(const StoreValue& v) override {
    StoreValue v2 = ((Closure*)g_.get())->Call(v);
    return ((Closure*)f_.get())->Call(v2);
  }
 private:
  std::shared_ptr<HeapValue> f_;
  std::shared_ptr<HeapValue> g_;
};

extern StoreValue op_compose(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_append_vec(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_append_list(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_eq(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_neq(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_le(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_ge(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_ls(const StoreValue& v1, const StoreValue& v2);
extern StoreValue op_gt(const StoreValue& v1, const StoreValue& v2);

} // namespace Bestrafer

#endif
