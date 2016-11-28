; Set the logic type
(set-logic BV)

; Variable declarations
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))

; Problem model: x > y > z
(assert (and 
		(bvugt x y)
		(bvugt y z)
	)
)

; Output constraints: z < x
(assert (bvult z x))

; Check satisfiability 
(check-sat)

; Get the model
(get-model)
