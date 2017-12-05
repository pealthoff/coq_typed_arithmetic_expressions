# Typed Arithmetic Expressions

## Grammar

t ::=   &nbsp;&nbsp;&nbsp; true<br />
        &nbsp;&nbsp;&nbsp;&nbsp;|&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;false<br />
        &nbsp;&nbsp;&nbsp;&nbsp;|&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;if t then t else t<br />
        &nbsp;&nbsp;&nbsp;&nbsp;|&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;0<br />
        &nbsp;&nbsp;&nbsp;&nbsp;|&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;succ t<br />
        &nbsp;&nbsp;&nbsp;&nbsp;|&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;pred t<br />
        &nbsp;&nbsp;&nbsp;&nbsp;|&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;iszero t<br />

v ::=   &nbsp;&nbsp;&nbsp; true<br />
        &nbsp;&nbsp;&nbsp;&nbsp;|&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;false<br />
        &nbsp;&nbsp;&nbsp;&nbsp;|&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;nv<br />

nv ::=   &nbsp;&nbsp;&nbsp;0<br />
        &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;|&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;succ nv<br />

## Evaluation on Booleans


                    ------------------------------                  (E_IfTrue)
                    if true then t1 else t2 -> t1
                    

                   -------------------------------                 (E_IfFalse)
                   if false then t1 else t2 -> t2
                   

                              t1 -> t1'
            ------------------------------------------------            (E_If)
            if t1 then t2 else t3 -> if t1' then t2 else t3

## Evaluation on Numeric Values



                              t1 -> t1'
                       ------------------------                     (E_Iszero)
                       iszero t1 -> iszero t1'
                         

                          -----------------                     (E_IszeroZero)
                          iszero 0 -> true
                          

                           numeric value v1
                      --------------------------                (E_IszeroSucc)
                      iszero (succ v1) -> false
                      
                              t1 -> t1'
                         --------------------                         (E_Succ)
                         succ t1 -> succ t1'
                         

                             ------------                         (E_PredZero)
                             pred 0 -> 0
                             

                           numeric value v1
                        ---------------------                     (E_PredSucc)
                        pred (succ v1) -> v1
                        

                              t1 -> t1'
                         --------------------                         (E_Pred)
                         pred t1 -> pred t1'



## Typing Relation


                           ----------------                            (T_True)
                             true : Bool
                             

                          -----------------                           (T_False)
                            false : Bool
                            

               t1 : Bool      t2 : T      t3 : T
             --------------------------------------------                (T_If)
                      if t1 then t2 else t3 : T
                      

                             ------------                              (T_Zero)
                               0 : Nat
                               

                              t1 : Nat
                          ------------------                           (T_Succ)
                            succ t1 : Nat
                            

                              t1 : Nat
                          ------------------                           (T_Pred)
                            pred t1 : Nat
                            

                              t1 : Nat
                        ---------------------                        (T_IsZero)
                          iszero t1 : Bool
                          
## Soundness

- Progress: t : T =⇒ (t = v) ∨ (t → t 0 )
- Preservation: (t : T ) ∧ (t → t 0 ) =⇒ (t 0 : T )