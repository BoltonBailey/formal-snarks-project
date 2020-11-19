import data.polynomial.basic
import data.polynomial.coeff
import data.polynomial.div
import data.polynomial.monomial

namespace polynomial

universes u

variables {F : Type u}
variables [ring F]

lemma mul_no_constant_no_constant (a b c : polynomial F) : (a.coeff 0 = 0) -> (a * b = c) -> (c.coeff 0 = 0) :=
assume (ha : a.coeff 0 = 0),
assume (heq : a * b = c),
have h1 : a.div_X * X + C 0 = a, 
    from (eq.subst ha a.div_X_mul_X_add),
have h2 : a.div_X * X + (0 : polynomial F) = a, 
    from (eq.subst (C_0 : C (0 : F) = 0) h1),
have h3 : a.div_X * X = a, 
    from (eq.trans (eq.symm (add_zero (a.div_X * X))) h2),
have h4 : a.div_X * X * b = a * b, 
    by rw h3,
have hdsd : a.div_X * b * X = a.div_X * (b * X),
    from mul_assoc a.div_X b X,
have hbar : X * b = b * X,
    from commute_X b,
have hbaz : a.div_X * (b * X) = a.div_X * (X * b),
    by rw hbar,
have hqux : a.div_X * X * b = a.div_X * (X * b),
    from mul_assoc a.div_X X b,
have h5 : a.div_X * b * X = a.div_X * X * b,
    from eq.trans (eq.trans hdsd hbaz) (eq.symm hqux), -- TODO replace with associativity logic and commute_X to generalize from F to all rings
have h6 : a.div_X * b * X = a * b,
    from eq.trans h5 h4,
have h7 : a.div_X * b * X = c,
    from eq.trans h6 heq,
have h8 : (a.div_X * b * X).coeff 0 = 0,
    from coeff_mul_X_zero (a.div_X * b),
show c.coeff 0 = 0,
    from eq.subst h7 h8

#check mul_no_constant_no_constant



end polynomial