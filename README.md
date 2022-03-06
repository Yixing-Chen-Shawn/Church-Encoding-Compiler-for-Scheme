# Church Encoding Compiler for Scheme

This is a compiler for a significant subset of Scheme to the lambda calculus.

To be very clear, inputs will look like this:

```
'(+ 1 1)
```

And it will output things that look like this:

```
'(((lambda (n)
    (lambda (k) 
      (lambda (f) (lambda (x) ((k f) ((n f) x))))))
	  (lambda (f) (lambda (x) (f x))))
  (lambda (f) (lambda (x) (f x))))
```

The tests then execute these lambda calculus terms and convert them
back to numbers/booleans as appropriate (using, e.g., `church->nat`).

## Input language

The input language will be given as S-expressions that have the
following structure:

```
e ::= (letrec ([x (lambda (x ...) e)]) e)
    | (let ([x e] ...) e)
    | (let* ([x e] ...) e)
    | (lambda (x ...) e)
    | (e e ...)
    | x
    | (and e ...) | (or e ...)
    | (if e e e)
    | (prim e) | (prim e e)
    | datum

datum ::= nat | (quote ()) | #t | #f
nat ::= 0 | 1 | 2 | ...
x is a symbol
prim is a primitive function.
```

The compiler supports let (with any number of bindings, including zero), let*, lambda, application, variables, and/or (short-circuiting as necessary), if, applications of unary and binary, primitive functions, and constants (called "datums").

Also supports the following primitive functions:

```
+ * - = add1 sub1 cons car cdr null? not zero?
```

The input language has semantics identical to Scheme / Racket, except:
 + All numbers will be naturals
 + will not be provided code that yields any kind of error in Racket
 + do not need to treat non-boolean values as #t at if, and, or forms
 + primitive operations are either strictly unary (add1 sub1 null? zero? not car cdr),
   or binary (+ - * = cons) rather than k-ary
 + There will be no variadic functions or applications---but any fixed arity is allowed

Implemented -, =, and sub1. Encodings for those functions for Excellent.

Letrec is implemented correctly using a fixed-point
combinator (such as the Y/Z combinator). 

## Output language:

The `church-compile` function will generate S-expressions in the lambda calculus:

e ::= (lambda (x) e)
    | (e e)
    | x
where x is a symbol representing a variable

## Tests

The following tests are required for minimal:

public-add
public-add1
public-arith0
public-arith1
public-bool0
public-bool1
public-bool2
public-curry
public-length
public-let0
public-let1
public-list0
public-list1
public-list2
public-multiply
public-zero

The following tests are required for satisfactory:

public-length-letrec
server-and
server-andor
server-append
server-or
server-reverse

The following tests are required for excellent:

public-arith-bonus
public-factorial-bonus
server-fib-bonus

