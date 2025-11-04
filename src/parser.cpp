/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Wrapper parse method that delegates to the underlying SyntaxBase
 */
Expr Syntax::parse(Assoc &env) {
    return ptr->parse(env);
}

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr SyntaxBase::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    //Check if the first element is a symbol
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // Not a symbol, use Apply
        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); i++) {
            args.push_back(stxs[i].parse(env));
        }
        return Expr(new Apply(stxs[0].parse(env), args));
    }

    string op = id->s;

    // Check if it's a primitive
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i].parse(env));
        }

        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() == 2) {
                return Expr(new Plus(parameters[0], parameters[1]));
            } else {
                return Expr(new PlusVar(parameters));
            }
        } else if (op_type == E_MINUS) {
            if (parameters.size() == 2) {
                return Expr(new Minus(parameters[0], parameters[1]));
            } else {
                return Expr(new MinusVar(parameters));
            }
        } else if (op_type == E_MUL) {
            if (parameters.size() == 2) {
                return Expr(new Mult(parameters[0], parameters[1]));
            } else {
                return Expr(new MultVar(parameters));
            }
        } else if (op_type == E_DIV) {
            if (parameters.size() == 2) {
                return Expr(new Div(parameters[0], parameters[1]));
            } else {
                return Expr(new DivVar(parameters));
            }
        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_EXPT) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for expt");
            }
            return Expr(new Expt(parameters[0], parameters[1]));
        } else if (op_type == E_LT) {
            if (parameters.size() == 2) {
                return Expr(new Less(parameters[0], parameters[1]));
            } else {
                return Expr(new LessVar(parameters));
            }
        } else if (op_type == E_LE) {
            if (parameters.size() == 2) {
                return Expr(new LessEq(parameters[0], parameters[1]));
            } else {
                return Expr(new LessEqVar(parameters));
            }
        } else if (op_type == E_EQ) {
            if (parameters.size() == 2) {
                return Expr(new Equal(parameters[0], parameters[1]));
            } else {
                return Expr(new EqualVar(parameters));
            }
        } else if (op_type == E_GE) {
            if (parameters.size() == 2) {
                return Expr(new GreaterEq(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterEqVar(parameters));
            }
        } else if (op_type == E_GT) {
            if (parameters.size() == 2) {
                return Expr(new Greater(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterVar(parameters));
            }
        } else if (op_type == E_CONS) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for cons");
            }
            return Expr(new Cons(parameters[0], parameters[1]));
        } else if (op_type == E_CAR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for car");
            }
            return Expr(new Car(parameters[0]));
        } else if (op_type == E_CDR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for cdr");
            }
            return Expr(new Cdr(parameters[0]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_SETCAR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-car!");
            }
            return Expr(new SetCar(parameters[0], parameters[1]));
        } else if (op_type == E_SETCDR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-cdr!");
            }
            return Expr(new SetCdr(parameters[0], parameters[1]));
        } else if (op_type == E_NOT) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for not");
            }
            return Expr(new Not(parameters[0]));
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if (op_type == E_EQQ) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for eq?");
            }
            return Expr(new IsEq(parameters[0], parameters[1]));
        } else if (op_type == E_BOOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for boolean?");
            }
            return Expr(new IsBoolean(parameters[0]));
        } else if (op_type == E_INTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for number?");
            }
            return Expr(new IsFixnum(parameters[0]));
        } else if (op_type == E_NULLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for null?");
            }
            return Expr(new IsNull(parameters[0]));
        } else if (op_type == E_PAIRQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for pair?");
            }
            return Expr(new IsPair(parameters[0]));
        } else if (op_type == E_PROCQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for procedure?");
            }
            return Expr(new IsProcedure(parameters[0]));
        } else if (op_type == E_SYMBOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for symbol?");
            }
            return Expr(new IsSymbol(parameters[0]));
        } else if (op_type == E_LISTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for list?");
            }
            return Expr(new IsList(parameters[0]));
        } else if (op_type == E_STRINGQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for string?");
            }
            return Expr(new IsString(parameters[0]));
        } else if (op_type == E_DISPLAY) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for display");
            }
            return Expr(new Display(parameters[0]));
        } else if (op_type == E_VOID) {
            if (parameters.size() != 0) {
                throw RuntimeError("Wrong number of arguments for void");
            }
            return Expr(new MakeVoid());
        } else if (op_type == E_EXIT) {
            if (parameters.size() != 0) {
                throw RuntimeError("Wrong number of arguments for exit");
            }
            return Expr(new Exit());
        }
    }

    // Check if it's a reserved word and has the right structure
    if (reserved_words.count(op) != 0) {
        ExprType reserved_type = reserved_words[op];

        // Check structure before treating as special form
        bool is_special_form = false;

        if (reserved_type == E_QUOTE && stxs.size() == 2) {
            is_special_form = true;
        } else if (reserved_type == E_BEGIN) {
            is_special_form = true;
        } else if (reserved_type == E_IF && stxs.size() == 4) {
            is_special_form = true;
        } else if (reserved_type == E_COND && stxs.size() >= 2) {
            is_special_form = true;
        } else if (reserved_type == E_LAMBDA && stxs.size() >= 3) {
            // Check if second element is a list (parameter list)
            if (dynamic_cast<List*>(stxs[1].get())) {
                is_special_form = true;
            }
        } else if (reserved_type == E_DEFINE && stxs.size() >= 3) {
            is_special_form = true;
        } else if (reserved_type == E_LET && stxs.size() >= 3) {
            // Check if second element is a list (bindings)
            if (dynamic_cast<List*>(stxs[1].get())) {
                is_special_form = true;
            }
        } else if (reserved_type == E_LETREC && stxs.size() >= 3) {
            // Check if second element is a list (bindings)
            if (dynamic_cast<List*>(stxs[1].get())) {
                is_special_form = true;
            }
        } else if (reserved_type == E_SET && stxs.size() == 3) {
            // Check if second element is a symbol
            if (dynamic_cast<SymbolSyntax*>(stxs[1].get())) {
                is_special_form = true;
            }
        }

        if (is_special_form) {
        switch (reserved_words[op]) {
            case E_QUOTE:
                return Expr(new Quote(stxs[1]));
            case E_BEGIN: {
                vector<Expr> exprs;
                for (size_t i = 1; i < stxs.size(); i++) {
                    exprs.push_back(stxs[i].parse(env));
                }
                return Expr(new Begin(exprs));
            }
            case E_IF:
                return Expr(new If(stxs[1].parse(env), stxs[2].parse(env), stxs[3].parse(env)));
            case E_COND: {
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); i++) {
                    List* clause_list = dynamic_cast<List*>(stxs[i].get());
                    if (!clause_list) {
                        throw RuntimeError("cond clause must be a list");
                    }
                    vector<Expr> clause;
                    for (auto& stx : clause_list->stxs) {
                        clause.push_back(stx.parse(env));
                    }
                    clauses.push_back(clause);
                }
                return Expr(new Cond(clauses));
            }
            case E_LAMBDA: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for lambda");
                }
                List* params_list = dynamic_cast<List*>(stxs[1].get());
                if (!params_list) {
                    throw RuntimeError("lambda parameters must be a list");
                }
                vector<string> params;
                for (auto& param : params_list->stxs) {
                    SymbolSyntax* param_sym = dynamic_cast<SymbolSyntax*>(param.get());
                    if (!param_sym) {
                        throw RuntimeError("lambda parameter must be a symbol");
                    }
                    params.push_back(param_sym->s);
                }
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i].parse(env));
                }
                Expr body = (body_exprs.size() == 1) ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Lambda(params, body));
            }
            case E_DEFINE: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for define");
                }
                SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (var_sym) {
                    // Simple variable definition
                    vector<Expr> value_exprs;
                    for (size_t i = 2; i < stxs.size(); i++) {
                        value_exprs.push_back(stxs[i].parse(env));
                    }
                    Expr value = (value_exprs.size() == 1) ? value_exprs[0] : Expr(new Begin(value_exprs));
                    return Expr(new Define(var_sym->s, value));
                } else {
                    // Function definition shorthand
                    List* func_def = dynamic_cast<List*>(stxs[1].get());
                    if (!func_def || func_def->stxs.empty()) {
                        throw RuntimeError("Invalid define syntax");
                    }
                    SymbolSyntax* func_name = dynamic_cast<SymbolSyntax*>(func_def->stxs[0].get());
                    if (!func_name) {
                        throw RuntimeError("Function name must be a symbol");
                    }
                    vector<string> params;
                    for (size_t i = 1; i < func_def->stxs.size(); i++) {
                        SymbolSyntax* param_sym = dynamic_cast<SymbolSyntax*>(func_def->stxs[i].get());
                        if (!param_sym) {
                            throw RuntimeError("Function parameter must be a symbol");
                        }
                        params.push_back(param_sym->s);
                    }
                    vector<Expr> body_exprs;
                    for (size_t i = 2; i < stxs.size(); i++) {
                        body_exprs.push_back(stxs[i].parse(env));
                    }
                    Expr body = (body_exprs.size() == 1) ? body_exprs[0] : Expr(new Begin(body_exprs));
                    return Expr(new Define(func_name->s, Expr(new Lambda(params, body))));
                }
            }
            case E_LET: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for let");
                }
                List* bindings_list = dynamic_cast<List*>(stxs[1].get());
                if (!bindings_list) {
                    throw RuntimeError("let bindings must be a list");
                }
                vector<pair<string, Expr>> bindings;
                for (auto& binding : bindings_list->stxs) {
                    List* bind_pair = dynamic_cast<List*>(binding.get());
                    if (!bind_pair || bind_pair->stxs.size() != 2) {
                        throw RuntimeError("let binding must be a pair");
                    }
                    SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(bind_pair->stxs[0].get());
                    if (!var_sym) {
                        throw RuntimeError("let variable must be a symbol");
                    }
                    bindings.push_back(mp(var_sym->s, bind_pair->stxs[1].parse(env)));
                }
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i].parse(env));
                }
                Expr body = (body_exprs.size() == 1) ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Let(bindings, body));
            }
            case E_LETREC: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for letrec");
                }
                List* bindings_list = dynamic_cast<List*>(stxs[1].get());
                if (!bindings_list) {
                    throw RuntimeError("letrec bindings must be a list");
                }
                vector<pair<string, Expr>> bindings;
                for (auto& binding : bindings_list->stxs) {
                    List* bind_pair = dynamic_cast<List*>(binding.get());
                    if (!bind_pair || bind_pair->stxs.size() != 2) {
                        throw RuntimeError("letrec binding must be a pair");
                    }
                    SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(bind_pair->stxs[0].get());
                    if (!var_sym) {
                        throw RuntimeError("letrec variable must be a symbol");
                    }
                    bindings.push_back(mp(var_sym->s, bind_pair->stxs[1].parse(env)));
                }
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i].parse(env));
                }
                Expr body = (body_exprs.size() == 1) ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Letrec(bindings, body));
            }
            case E_SET: {
                SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (!var_sym) {
                    throw RuntimeError("set! variable must be a symbol");
                }
                return Expr(new Set(var_sym->s, stxs[2].parse(env)));
            }
            default:
                throw RuntimeError("Unknown reserved word: " + op);
        }
        }
    }

    // Default: use Apply
    vector<Expr> args;
    for (size_t i = 1; i < stxs.size(); i++) {
        args.push_back(stxs[i].parse(env));
    }
    return Expr(new Apply(stxs[0].parse(env), args));
}
