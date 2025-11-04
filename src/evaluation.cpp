/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    for (auto& rand : rands) {
        args.push_back(rand->eval(e));
    }
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    // TODO: TO identify the invalid variable
    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError
    
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
             static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                    {E_VOID,     {new MakeVoid(), {}}},
                    {E_EXIT,     {new Exit(), {}}},
                    {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                    {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                    {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                    {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                    {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                    {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                    {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQQ,      {new EqualVar({}), {}}},
            };

            auto it = primitive_map.find(primitives[x]);
            if (it != primitive_map.end()) {
                return ProcedureV(it->second.second, it->second.first, e);
            }
      }
    }
    return matched_value;
}

// Forward declaration of gcd (defined in expr.cpp)
extern int gcd(int a, int b);

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 + n2);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        int num = r1->numerator + n2 * r1->denominator;
        int den = r1->denominator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = n1 * r2->denominator + r2->numerator;
        int den = r2->denominator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = r1->numerator * r2->denominator + r2->numerator * r1->denominator;
        int den = r1->denominator * r2->denominator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 - n2);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        int num = r1->numerator - n2 * r1->denominator;
        int den = r1->denominator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = n1 * r2->denominator - r2->numerator;
        int den = r2->denominator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = r1->numerator * r2->denominator - r2->numerator * r1->denominator;
        int den = r1->denominator * r2->denominator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 * n2);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        int num = r1->numerator * n2;
        int den = r1->denominator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = n1 * r2->numerator;
        int den = r2->denominator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = r1->numerator * r2->numerator;
        int den = r1->denominator * r2->denominator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        int g = gcd(abs(n1), abs(n2));
        int num = n1 / g;
        int den = n2 / g;
        if (den < 0) { num = -num; den = -den; }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        int num = r1->numerator;
        int den = r1->denominator * n2;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den < 0) { num = -num; den = -den; }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        int num = n1 * r2->denominator;
        int den = r2->numerator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den < 0) { num = -num; den = -den; }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        int num = r1->numerator * r2->denominator;
        int den = r1->denominator * r2->numerator;
        int g = gcd(abs(num), abs(den));
        num /= g;
        den /= g;
        if (den < 0) { num = -num; den = -den; }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    if (args.empty()) return IntegerV(0);
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        Plus plus_op(Expr(new Fixnum(0)), Expr(new Fixnum(0)));
        result = plus_op.evalRator(result, args[i]);
    }
    return result;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.empty()) throw RuntimeError("- requires at least 1 argument");
    if (args.size() == 1) {
        // Negate
        if (args[0]->v_type == V_INT) {
            return IntegerV(-dynamic_cast<Integer*>(args[0].get())->n);
        } else if (args[0]->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            return RationalV(-r->numerator, r->denominator);
        }
        throw RuntimeError("Wrong typename");
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        Minus minus_op(Expr(new Fixnum(0)), Expr(new Fixnum(0)));
        result = minus_op.evalRator(result, args[i]);
    }
    return result;
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.empty()) return IntegerV(1);
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        Mult mult_op(Expr(new Fixnum(0)), Expr(new Fixnum(0)));
        result = mult_op.evalRator(result, args[i]);
    }
    return result;
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.empty()) throw RuntimeError("/ requires at least 1 argument");
    if (args.size() == 1) {
        // Reciprocal
        if (args[0]->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(args[0].get())->n;
            if (n == 0) throw RuntimeError("Division by zero");
            if (n == 1) return IntegerV(1);
            if (n == -1) return IntegerV(-1);
            return RationalV(1, n);
        } else if (args[0]->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            if (r->numerator == 0) throw RuntimeError("Division by zero");
            int num = r->denominator;
            int den = r->numerator;
            if (den < 0) { num = -num; den = -den; }
            if (den == 1) return IntegerV(num);
            return RationalV(num, den);
        }
        throw RuntimeError("Wrong typename");
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        Div div_op(Expr(new Fixnum(0)), Expr(new Fixnum(0)));
        result = div_op.evalRator(result, args[i]);
    }
    return result;
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    return BooleanV(compareNumericValues(rand1, rand2) <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) >= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) > 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) != 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) < 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) <= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    Value result = NullV();
    for (int i = args.size() - 1; i >= 0; i--) {
        result = PairV(args[i], result);
    }
    return result;
}

Value IsList::evalRator(const Value &rand) { // list?
    if (rand->v_type == V_NULL) return BooleanV(true);
    if (rand->v_type != V_PAIR) return BooleanV(false);

    Value current = rand;
    while (current->v_type == V_PAIR) {
        Pair* p = dynamic_cast<Pair*>(current.get());
        current = p->cdr;
    }
    return BooleanV(current->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("car requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("cdr requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-car! requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-cdr! requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

// Helper function to convert syntax to value
Value syntaxToValue(const Syntax& s) {
    if (auto num = dynamic_cast<Number*>(s.get())) {
        return IntegerV(num->n);
    } else if (auto rat = dynamic_cast<RationalSyntax*>(s.get())) {
        return RationalV(rat->numerator, rat->denominator);
    } else if (dynamic_cast<TrueSyntax*>(s.get())) {
        return BooleanV(true);
    } else if (dynamic_cast<FalseSyntax*>(s.get())) {
        return BooleanV(false);
    } else if (auto sym = dynamic_cast<SymbolSyntax*>(s.get())) {
        return SymbolV(sym->s);
    } else if (auto str = dynamic_cast<StringSyntax*>(s.get())) {
        return StringV(str->s);
    } else if (auto lst = dynamic_cast<List*>(s.get())) {
        if (lst->stxs.empty()) {
            return NullV();
        }
        Value result = NullV();
        for (int i = lst->stxs.size() - 1; i >= 0; i--) {
            result = PairV(syntaxToValue(lst->stxs[i]), result);
        }
        return result;
    }
    throw RuntimeError("Unknown syntax type in quote");
}

Value Begin::eval(Assoc &e) {
    if (es.empty()) return VoidV();
    Value result = VoidV();
    for (auto& expr : es) {
        result = expr->eval(e);
    }
    return result;
}

Value Quote::eval(Assoc& e) {
    return syntaxToValue(s);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) return BooleanV(true);
    Value result = BooleanV(true);
    for (auto& rand : rands) {
        result = rand->eval(e);
        if (result->v_type == V_BOOL && !dynamic_cast<Boolean*>(result.get())->b) {
            return BooleanV(false);
        }
    }
    return result;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) return BooleanV(false);
    for (auto& rand : rands) {
        Value result = rand->eval(e);
        if (result->v_type != V_BOOL || dynamic_cast<Boolean*>(result.get())->b) {
            return result;
        }
    }
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    if (rand->v_type == V_BOOL && !dynamic_cast<Boolean*>(rand.get())->b) {
        return BooleanV(true);
    }
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    Value cond_val = cond->eval(e);
    bool is_true = true;
    if (cond_val->v_type == V_BOOL && !dynamic_cast<Boolean*>(cond_val.get())->b) {
        is_true = false;
    }
    if (is_true) {
        return conseq->eval(e);
    } else {
        return alter->eval(e);
    }
}

Value Cond::eval(Assoc &env) {
    for (auto& clause : clauses) {
        if (clause.empty()) continue;

        // Check if it's an else clause
        if (auto var_expr = dynamic_cast<Var*>(clause[0].get())) {
            if (var_expr->x == "else") {
                if (clause.size() == 1) {
                    return VoidV();
                }
                Value result = VoidV();
                for (size_t i = 1; i < clause.size(); i++) {
                    result = clause[i]->eval(env);
                }
                return result;
            }
        }

        Value cond_val = clause[0]->eval(env);
        bool is_true = true;
        if (cond_val->v_type == V_BOOL && !dynamic_cast<Boolean*>(cond_val.get())->b) {
            is_true = false;
        }

        if (is_true) {
            if (clause.size() == 1) {
                return cond_val;
            }
            Value result = VoidV();
            for (size_t i = 1; i < clause.size(); i++) {
                result = clause[i]->eval(env);
            }
            return result;
        }
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value proc_val = rator->eval(e);
    if (proc_val->v_type != V_PROC) {
        throw RuntimeError("Attempt to apply a non-procedure");
    }

    Procedure* clos_ptr = dynamic_cast<Procedure*>(proc_val.get());

    std::vector<Value> args;
    for (auto& arg_expr : rand) {
        args.push_back(arg_expr->eval(e));
    }

    if (args.size() != clos_ptr->parameters.size()) {
        throw RuntimeError("Wrong number of arguments");
    }

    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < args.size(); i++) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // Evaluate the expression
    Value val = e->eval(env);

    // Update or create the binding
    modify(var, val, env);

    return VoidV();
}

Value Let::eval(Assoc &env) {
    // Evaluate all binding values in the current environment
    std::vector<Value> values;
    for (auto& binding : bind) {
        values.push_back(binding.second->eval(env));
    }

    // Create new environment with bindings
    Assoc new_env = env;
    for (size_t i = 0; i < bind.size(); i++) {
        new_env = extend(bind[i].first, values[i], new_env);
    }

    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    // Create new environment with placeholder bindings
    Assoc new_env = env;
    for (auto& binding : bind) {
        new_env = extend(binding.first, VoidV(), new_env);
    }

    // Evaluate all binding values in the new environment
    std::vector<Value> values;
    for (auto& binding : bind) {
        values.push_back(binding.second->eval(new_env));
    }

    // Update bindings with actual values
    for (size_t i = 0; i < bind.size(); i++) {
        modify(bind[i].first, values[i], new_env);
    }

    return body->eval(new_env);
}

Value Set::eval(Assoc &env) {
    Value existing = find(var, env);
    if (existing.get() == nullptr) {
        throw RuntimeError("Undefined variable: " + var);
    }
    Value val = e->eval(env);
    modify(var, val, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}
