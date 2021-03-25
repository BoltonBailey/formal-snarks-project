import data.mv_polynomial.basic


open mv_polynomial
section


universes u

variables {F : Type u}
variables [field F]

noncomputable theory



parameter {vars : Type}
parameter [decidable_eq vars]



-- One way to prove this might be to establish an isomorphism between F[X, Y, Z] and F Y, Z, over X then use the univariate polynomial theorem over the ring F[Y, Z]?



def increment (f : vars →₀ ℕ) (s : vars) : (vars →₀ ℕ) :=
f + finsupp.single s 1

def decrement (f : vars →₀ ℕ) (s : vars) : (vars →₀ ℕ) :=
f - finsupp.single s 1

-- If two finitely supported functions at both > 0 at s
-- And their decrements on s are equal,
-- then they are equal
lemma equal_dec_equal (s : vars) (f : vars →₀ ℕ) (g : vars →₀ ℕ) (hf : f s > 0) (hg : g s > 0) (hxy : decrement f s = decrement g s) : f = g
:=
begin
  apply finsupp.ext,
  intro a,

  by_cases (s = a),
    -- h : s = a  
    have sa1: (finsupp.single s 1) a = 1,
      rw h,
      rw finsupp.single_apply,
      rw if_pos,
      refl,
      -- from eq.trans finsupp.single_apply (if_pos h),
    have h1f: f a = (decrement f s) a + 1,
    have h2f: (decrement f s) a + 1 = f a - (finsupp.single s 1) a + 1,
      from rfl,
    have h3f: (decrement f s) a + 1 = f a - 1 + 1,
      by rw [h2f, sa1],
    have h4f: f a = f a - 1 + 1,
      by rw [eq.symm h, (nat.sub_add_cancel hf)],
      exact eq.trans h4f (eq.symm h3f),
    have h1g: g a = (decrement g s) a + 1,
    have h2g: (decrement g s) a + 1 = g a - (finsupp.single s 1) a + 1,
      from rfl,
    have h3g: (decrement g s) a + 1 = g a - 1 + 1,
      by rw [h2g, sa1],
    have h4g: g a = g a - 1 + 1,
      by rw [eq.symm h, (nat.sub_add_cancel hg)],
      exact eq.trans h4g (eq.symm h3g),
    have hfg: f a = (decrement g s) a + 1,
      by rw [(eq.symm hxy), h1f],
    exact eq.trans hfg (eq.symm h1g),
    -- h : ¬s = a
    have sa1: (finsupp.single s 1) a = 0,
      rw finsupp.single_apply,
      rw if_neg,
      exact h,
      -- from eq.trans finsupp.single_apply (if_neg h),
    have h2f: (decrement f s) a + 1 = f a - (finsupp.single s 1) a + 1,
      from rfl,
    have h3f: (decrement f s) a + 1 = f a + 1,
      by rw [h2f, sa1, nat.sub_zero],
    have h4f: (decrement f s) a = f a,
      from nat.add_right_cancel h3f,
    have h2g: (decrement g s) a + 1 = g a - (finsupp.single s 1) a + 1,
      from rfl,
    have h3g: (decrement g s) a + 1 = g a + 1,
      by rw [h2g, sa1, nat.sub_zero],
    have h4g: (decrement g s) a = g a,
      from nat.add_right_cancel h3g,
    have hfg: f a = (decrement g s) a,
      by rw [(eq.symm hxy), h4f],
    exact eq.trans hfg h4g,
end

lemma inc_dec_nonzero_equal (s : vars) (f : vars →₀ ℕ) (hf : f s > 0) : increment (decrement f s) s = f :=
begin
  apply finsupp.ext,
  intro a,

  by_cases (s = a),
  rw (eq.symm h),
  have h2 : (increment (decrement f s) s) s = f  s - (finsupp.single s 1) s + (finsupp.single s 1) s,
  from rfl,
  rw h2,
  have h3 : finsupp.single s 1 s = 1,
  from finsupp.single_eq_same,
  rw h3,
  rw nat.sub_add_cancel hf,
  -- a ≠ s
  have h2 : (increment (decrement f s) s) a = f a - (finsupp.single s 1) a + (finsupp.single s 1) a,  
  from rfl,
  rw h2,
  have h3 : finsupp.single s 1 a = 0,
  from finsupp.single_eq_of_ne h,
  rw h3,
  from rfl,
end

lemma dec_inc_equal (s : vars) (f : vars →₀ ℕ) : decrement (increment f s) s = f :=
begin
  apply finsupp.ext,
  intro a,

  by_cases (s = a),
  rw (eq.symm h),
  have h2 : (decrement (increment f s) s) s = f  s + (finsupp.single s 1) s - (finsupp.single s 1) s,
  from rfl,
  rw h2,
  have h3 : finsupp.single s 1 s = 1,
  from finsupp.single_eq_same,
  rw h3,
  rw nat.add_sub_cancel,
  -- a ≠ s
  have h2 : (decrement (increment f s) s) a = f a + (finsupp.single s 1) a - (finsupp.single s 1) a,  
  from rfl,
  rw h2,
  have h3 : finsupp.single s 1 a = 0,
  from finsupp.single_eq_of_ne h,
  rw h3,
  from rfl,
end


lemma pos_of_ne_zero {n : nat} : n ≠ 0 → n > 0 :=
or.resolve_left (nat.eq_zero_or_pos n)

-- the div_X function in data.polynomial.div returns a polynomial in the form of a curly-brace enclosed support, to_fun, mem_support_to_fun
-- This is because a polynomial is defined as an add_monoid_algebra, which is a finsupp function, which has these three fields
-- Explicity
--   support is the support of the function
--   to_fun is the function itself
--   mem_support_to_fun is the proof that the function is nonzero exacly on it's defined support
-- Frankly, this function should be generalized to all mv_polynomials
-- Not just mv_polynomials over vars
-- TODO generalize this method and add to mathlib candidates folder
def div_X_v2 (p : mv_polynomial vars F) (s : vars) (h : (∀ m : vars →₀ ℕ, m s = 0 -> p.coeff m = 0)) : (mv_polynomial vars F) :=
{ to_fun := λ m, p.coeff (increment m s),
  support := p.support.image (λ m, decrement m s), 
  mem_support_to_fun := begin
    intro a,
    apply iff.intro,
    -- Forward impolication
    intro h1,
    have h2 := finset.mem_image.1 h1,
    rcases h2 with ⟨a_1, H, h3⟩,
    rw eq.symm h3,
    clear h3,
    clear h1,
    have h4 : p.coeff a_1 ≠ 0,
      from (p.mem_support_to_fun a_1).1 H,
    clear H,
    -- by the contrapositive of h and h4, a_1 s is not zero
    suffices h6: increment ( decrement a_1 s) s = a_1,
      rw h6,
      exact h4,
    have h7 : a_1 s ≠ 0,
      intro foo,
      apply h4,
      apply h,
      exact foo,
    -- use h7 and a lemma
    have h8 := pos_of_ne_zero h7,
    exact inc_dec_nonzero_equal s a_1 h8,
    --
    intro h1,
    apply finset.mem_image.2,
    -- 
    apply exists.intro (increment a s),
    apply exists.intro,
    exact (p.mem_support_to_fun (increment a s)).2 h1,
    exact dec_inc_equal s a,

  end
}

/-- In the product of a polynomial with a variable, the coefficients of all terms without that variable are zero -/
lemma mul_var_no_constant (a : mv_polynomial vars F) (s : vars) (m : vars →₀ ℕ):
m s = 0 -> (a * X s).coeff m = 0
:=
begin
  intro hc,
  have h13 := coeff_mul_X' m s a,
  rw h13,
  clear h13,
  have h14 : s ∉ m.support,
  intro a_1,
  exact ((m.mem_support_to_fun s).1 a_1) hc,
  apply if_neg,
  exact h14,
end

-- TODO: the converse of the above statement

lemma left_cancel_X_mul {a b : mv_polynomial vars F} (s : vars) :
X s * a = X s * b -> a = b
:=
begin
  intro h,
  rw ext_iff,
  intro m,
  rw ← coeff_mul_X m s a,
  rw ← coeff_mul_X m s b,
  rw mul_comm,
  rw h,
  rw mul_comm,  
end



-- For all monomials with no X component, the coefficient of a is zero
-- a * b = c
-- then for all monomials with no X component, the coefficient of a is zero
lemma mul_no_constant_no_constant (a b c : mv_polynomial vars F) (s : vars) : 
(∀ m : vars →₀ ℕ, m s = 0 -> a.coeff m = 0) -> (a * b = c) -> (∀ m : vars →₀ ℕ, m s = 0 -> c.coeff m = 0) 
:=
begin
  intros ha heq,
  intros m hc,
  let a_div_X : mv_polynomial vars F := div_X_v2 a s ha,
  have h1 : a_div_X * (X s) = a,
  apply (ext_iff (a_div_X * (X s)) a).2,
  intro,
  rw coeff_mul_X',
  by_cases s ∈ m_1.support,
  have h2 : a_div_X.coeff (m_1 - finsupp.single s 1)  = a.coeff m_1,
  have h3 : a_div_X.coeff (m_1 - finsupp.single s 1)  = a.coeff (increment (m_1 - finsupp.single s 1) s),
  refl,
  rw h3,
  clear h3,
  have h4: a.coeff (increment (m_1 - finsupp.single s 1) s) = a.coeff (increment (decrement m_1 s) s),
  refl,
  rw h4,
  clear h4,
  have h5 : m_1 s ≠ 0, 
  exact (m_1.mem_support_to_fun s).1 h,
  have h6 : increment (decrement m_1 s) s = m_1,
  exact inc_dec_nonzero_equal s m_1 (pos_of_ne_zero h5),
  rw h6,
  rw h2,
  clear h2,
  apply if_pos,
  exact h,
  have h7: a.coeff m_1 = 0,
  apply ha,
  by_contradiction a_1,
  apply h ((m_1.mem_support_to_fun s).2 a_1),
  rw h7,
  apply if_neg,
  exact h,

  have h4 : a_div_X * (X s) * b = c,
  rw h1,
  exact heq,
  clear h1,
  have h8 : X s * b = b * X s,
  apply mul_comm,
  have h9 : a_div_X * X s * b = a_div_X * (X s * b),
  apply mul_assoc,
  have h10 : a_div_X * (X s * b) = a_div_X * (b * X s),
  rw h8,
  have h11 : a_div_X * b * X s = a_div_X * (b * X s),
  apply mul_assoc,
  have h12 : a_div_X * X s * b = a_div_X * b * X s ,
  rw [h9, h10, eq.symm h11],
  clear h8 h9 h10 h11,

  rw eq.symm h4,
  rw h12,

  apply mul_var_no_constant,
  exact hc,
end

end

