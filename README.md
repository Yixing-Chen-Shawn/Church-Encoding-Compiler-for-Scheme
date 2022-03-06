# Project 2: Church Encoding Compiler for Scheme

In this project, you will implement a compiler for a significant
subset of Scheme to the lambda calculus. In other words, you will
write a function `church-compile`, which accepts as input a Scheme
expression (defined below) and generates as output an S-expression
corresponding to a lambda calculus term (in the style we have shown in
class). To test your code, we then convert the output of your function
to Racket using `eval` (a construct that allows us to convert an
S-expression to Racket code to execute).

To be very clear, you will receive inputs that look like this (further
specified below):

```
'(+ 1 1)
```

And you will output things that look like this:

```
'(((lambda (n)
    (lambda (k) 
      (lambda (f) (lambda (x) ((k f) ((n f) x))))))
	  (lambda (f) (lambda (x) (f x))))
  (lambda (f) (lambda (x) (f x))))
```

Our tests then execute these lambda calculus terms and convert them
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

In other words, you must support let (with any number of bindings,
including zero), let*, lambda, application, variables, and/or
(short-circuiting as necessary), if, applications of unary and binary
primitive functions, and constants (called "datums").

You must support the following primitive functions:

```
+ * - = add1 sub1 cons car cdr null? not zero?
```

Your input language has semantics identical to Scheme / Racket, except:
 + All numbers will be naturals
 + You will not be provided code that yields any kind of error in Racket
 + You do not need to treat non-boolean values as #t at if, and, or forms
 + primitive operations are either strictly unary (add1 sub1 null? zero? not car cdr),
   or binary (+ - * = cons) rather than k-ary
 + There will be no variadic functions or applications---but any fixed arity is allowed

To get *excellent* in this project, you must implement -, =, and
sub1. Encodings for those functions are not given in the slides in
class, but they can be looked up online (or puzzled out for yourself).

Note that implementing letrec correctly involves using a fixed-point
combinator (such as the Y/Z combinator). We will discuss this
transformation in class and give hints.

## Output language:

Your `church-compile` function should generate S-expressions in the lambda calculus:

e ::= (lambda (x) e)
    | (e e)
    | x
where x is a symbol? representing a variable

## Advice and Helpful Hints

You should be watching the lectures on Church encoding to help you do
this project. If you do not understand those videos, it's going to be
very hard to do this project.

Once you understand the videos on Church encoding, you should
concentrate on implementing the function `churchify`, which does the
bulk amount of the work. This statement is a big `match` statement
that decides how to translate an expression from the input language to
the lambda calculus.

I recommend you start as follows: implement numbers and primitive
operations over those numbers in the function `churchify`. As you do
this, you should be calling `churchify` with your own small test
cases. This is a crucial development and debugging workflow I think
will make your work much quicker. Once you figure out how to do
numbers and applications of unary and boolean primitives to numbers,
work on implementing let of variable arity. Be careful to also
implement let of 0-arity, `(let () 2)` should still work!

This project should not necessarily require a lot of code. Our
reference `churchify` function is implemented in a way that allows it
to call itself to recursively construct other lambda expressions, and
thus is implemented in only ~25-30 lines of code (plus additional
definitions for builtins). You should not find yourself writing a lot
of code.

## Grading

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

