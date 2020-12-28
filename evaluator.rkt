#lang racket

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (eval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))
      (eval (if-consecuent exp) env)
      (eval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env)
  'ok)

(define (eval-definition exp env)
  (define-variable!
    (definition-variable exp)
    (eval (definition-value exp) env)
    env)
  'ok)

(define (self-evaluating? exp)
  (or (number? exp) (string? exp)))

(define variable? symbol?)

(define (tagged-list? exp tag)
  (and (pair? exp) (eq? (car exp) tag)))

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define text-of-quotation cadr)

(define (assignment? exp)
  (tagged-list? exp 'set!))

(define assignment-variable cadr)

(define assignment-value caddr)

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp) ; formal parameters
                   (cddr exp)))) ; body

(define (lambda? exp) (tagged-list? exp 'lambda))

(define lambda-parameters cadr)

(define lambda-body cddr)

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (if? exp) (tagged-list? exp 'if))

(define if-predicate cadr)

(define if-consecuent caddr)

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

(define (begin? exp) (tagged-list? exp 'begin))

(define begin-actions cdr)

(define (last-exp? seq) (null? (cdr seq)))

(define first-exp car)

(define rest-exps cdr)

(define (make-begin seq) (cons 'begin seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define application? pair?)

(define make-applicaton cons)

(define operator car)

(define operands cdr)

(define no-operands? null?)

(define first-operand car)

(define rest-operands cdr)

(define (let? exp) (tagged-list? exp 'let))

(define let-assignments cadr)

(define let-body cddr)

(define (make-assignment var exp) (list var exp))

(define (expand-let assignments body)
  (let ((parameters (map assignment-variable assignments))
        (arguments (map assignment-value assignments)))
    (cons (make-lambda parameters body) arguments)))

(define (let->combination exp)
  (expand-let (let-assignments exp) (let-body exp)))

(define (make-let assignments body)
  (cons 'let (cons assignments body)))

(define (let*? exp) (tagged-list? exp 'let*))

(define let*-assignments cadr)

(define let*-body cddr)

(define (expand-let* assignments body)
  (if (null? assignments)
      body
      (let ((var (assignment-variable (car assignments)))
            (val (assignment-value (car assignments))))
        (make-let (make-assignment var val)
                  (expand-let* (cdr assignments) body)))))

(define (let*->nested-lets exp)
  (expand-let* (let*-assignments exp) (let*-body exp)))

(define (cond? exp) (tagged-list? exp 'cond))

(define cond-clauses cdr)

(define cond-predicate car)

(define cond-actions cdr)

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define cond-recipient caddr)

(define cond-arrow cadr)

(define (cond-extended-clause? clause)
  (and (eq? (cond-arrow clause) '=>) (not (null? (cond-recipient clause)))))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (cond ((cond-else-clause? first)
               (if (null? rest)
                   (sequence->exp (cond-actions first))
                   (error "ELSE clause isn't last -- COND->IF" clauses)))
              ((cond-extended-clause? first)
               (make-if (cond-predicate first)
                        (make-application (cond-recipient first) (list (cond-predicate first)))
                        (expand-clauses rest)))
              (else
               (make-if (cond-predicate first)
                        (sequence->exp (cond-actions first))
                        (expand-clauses rest)))))))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (and? exp) (tagged-list? exp 'and))

(define and-operands cdr)

(define (eval-and exp env)
  (cond ((null? exp) 'true)
        ((false? (eval (car exp) env)) 'false)
        (else (eval-and (cdr exp) env))))

(define (or? exp) (tagged-list? exp 'or))

(define or-operands cdr)

(define (eval-or exp env)
  (cond ((null? exp) 'false)
        ((true? (eval (car exp) env)) 'true)
        (else (eval-or (cdr exp) env))))

(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((quoted? exp) (text-of-quotation exp))
        ((assignment? exp) (eval-assignment exp env))
        ((definition? exp) (eval-definition exp env))
        ((if? exp) (eval-if exp env))
        ((let? exp) (eval (let->combination exp) env))
        ((let*? exp) (eval (let*->nested-lets exp) env))
        ((lambda? exp)
         (make-procedure (lambda-parameters exp)
                         (lambda-body exp)
                         env))
        ((begin? exp)
         (eval-sequence (begin-actions exp) env))
        ((cond? exp) (eval (cond->if exp) env))
        ((and? exp) (eval-and (and-operands exp) env))
        ((or? exp) (eval-or (or-operands exp) env))
        ((application? exp)
         (apply (eval (operator exp) env)
                (list-of-values (operands exp) env)))
        (else
         (error "Unknown expression type -- EVAL" exp))))

(define (apply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((compound-procedure? procedure)
         (eval-sequence (procedure-body procedure)
                        (extend-environment (procedure-parameters procedure)
                                            arguments
                                            (procedure-environment procedure))))
        (else
         (error "Unknown procedure type -- APPLY" procedure))))
