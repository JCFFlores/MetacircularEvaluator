#lang racket

(provide compound-procedure?
         procedure-parameters
         procedure-body
         setup-environment
         eval)

(require compatibility/mlist)

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (eval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

(define (true? x) (not (eq? x false)))

(define (false? x) (eq? x false))

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

(define assignment-variable car)

(define assignment-value cadr)

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

(define (make-define-procedure name parameters body)
  (cons 'define (cons (cons name parameters) body)))

(define (make-unbound!? exp)
  (tagged-list? exp 'make-unbound!))

(define make-unbound!-binding cadr)

(define (eval-make-unbound! var env)
  (define (remove-binding vars vals)
    (cond ((null? vars)
           (error "Unbound variable -- MAKE-UNBOUND!" var))
          ((eq? var (mcar vars)) (mcons (mcdr vars) (mcdr vals)))
          (else
           (let* ((data (remove-binding (mcdr vars) (mcdr vals)))
                  (clean-vars (mcons (mcar vars) (mcar data)))
                  (clean-vals (mcons (mcar vals) (mcdr data))))
             (make-frame clean-vars clean-vals)))))
  (let ((frame (first-frame env)))
    (set-mcar! env (remove-binding (frame-variables frame) (frame-values frame))))
  'ok)

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

(define make-application cons)

(define operator car)

(define operands cdr)

(define no-operands? null?)

(define first-operand car)

(define rest-operands cdr)

(define (let? exp) (tagged-list? exp 'let))

(define let-assignments cadr)

(define let-body cddr)

(define named-let-var cadr)

(define named-let-bindings caddr)

(define named-let-body cdddr)

(define (named-let? exp)
  (variable? (named-let-var exp)))

(define (expand-named-let var bindings body)
  (let ((parameters (map assignment-variable bindings))
        (arguments (map assignment-value bindings)))
    (sequence->exp (list
                    (make-define-procedure var parameters body)
                    (make-application var arguments)))))

(define (make-assignment var exp) (list var exp))

(define (expand-let assignments body)
  (let ((parameters (map assignment-variable assignments))
        (arguments (map assignment-value assignments)))
    (make-application (make-lambda parameters body) arguments)))

(define (let->combination exp)
  (if (named-let? exp)
      (expand-named-let (named-let-var exp) (named-let-bindings exp) (named-let-body exp))
      (expand-let (let-assignments exp) (let-body exp))))

(define (make-let assignments body)
  (cons 'let (cons assignments body)))

(define (let*? exp) (tagged-list? exp 'let*))

(define let*-assignments cadr)

(define let*-body cddr)

(define (last-assignment? assignments) (null? (cdr assignments)))

(define (expand-let* assignments body)
  (if (last-assignment? assignments)
      (make-let assignments body)
      (let* ((assignment (car assignments))
             (var (assignment-variable assignment))
             (val (assignment-value assignment)))
        (make-let (list (make-assignment var val))
                  (list (expand-let* (cdr assignments) body))))))

(define (let*->nested-lets exp)
  (let ((assignments (let*-assignments exp)))
    (if (null? assignments)
        (error "Empty bindings -- LET*" exp)
        (expand-let* assignments (let*-body exp)))))

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
  (cond ((null? exp) true)
        ((false? (eval (car exp) env)) false)
        (else (eval-and (cdr exp) env))))

(define (or? exp) (tagged-list? exp 'or))

(define or-operands cdr)

(define (eval-or exp env)
  (cond ((null? exp) false)
        ((true? (eval (car exp) env)) true)
        (else (eval-or (cdr exp) env))))

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (compound-procedure? p)
  (tagged-list? p 'procedure))

(define procedure-parameters cadr)

(define procedure-body caddr)

(define procedure-environment cadddr)

(define enclosing-environment mcdr)

(define first-frame mcar)

(define the-empty-environment '())

(define (to-mlist l)
  (cond ((mlist? l) l)
        ((list? l) (list->mlist l))
        (else (error "Can't convert to mlist" l))))

(define (make-frame variables values)
  (mcons (to-mlist variables) (to-mlist values)))

(define frame-variables mcar)

(define frame-values mcdr)

(define (add-binding-to-frame! var val frame)
  (set-mcar! frame (mcons var (mcar frame)))
  (set-mcdr! frame (mcons val (mcdr frame))))

(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (mcons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars) (env-loop (enclosing-environment env)))
            ((eq? var (mcar vars)) (mcar vals))
            (else (scan (mcdr vars) (mcdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars) (env-loop (enclosing-environment env)))
            ((eq? var (mcar vars)) (set-mcar! vals val))
            (else (scan (mcdr vars) (mcdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars) (add-binding-to-frame! var val frame))
            ((eq? var (mcar vars)) (set-mcar! vals val))
            (else (scan (mcdr vars) (mcdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define primitive-implementation cadr)

(define primitive-procedures
  (list (list 'car mcar)
        (list 'cdr mcdr)
        (list 'cons mcons)
        (list 'set-car! set-mcar!)
        (list 'set-cdr! set-mcdr!)
        (list 'null? null?)
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '/ /)
        (list '= =)))

(define (primitive-procedure-names)
  (map car primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc))) primitive-procedures))

(define (apply-primitive-procedure proc args)
  (apply (primitive-implementation proc) args))

(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    initial-env))

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
        ((make-unbound!? exp) (eval-make-unbound! (make-unbound!-binding exp) env))
        ((application? exp)
         (apply-exercise (eval (operator exp) env)
                (list-of-values (operands exp) env)))
        (else
         (error "Unknown expression type -- EVAL" exp))))

(define (apply-exercise procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((compound-procedure? procedure)
         (eval-sequence (procedure-body procedure)
                        (extend-environment (procedure-parameters procedure)
                                            arguments
                                            (procedure-environment procedure))))
        (else
         (error "Unknown procedure type -- APPLY" procedure))))
