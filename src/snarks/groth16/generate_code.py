

def f1():
    for a in range(3):
        for b in range(3):
            for d in range(5):
                for g in range(5):
                    if a + b > 2:
                        continue
                    if abs(d-2) + abs(g-2) > 2:
                        continue
                    string = f"""lemma coeff{a}{b}{d}{g} (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
1 = 0 :=
begin
rw verified' at eqn,
rw [A', B', C'] at eqn,
simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
have congr_coeff{a}{b}{d}{g} := congr_arg (coeff (single vars.α {a} + single vars.β {b} + single vars.δ {d} + single vars.γ {g})) eqn,
clear eqn,
simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff{a}{b}{d}{g},
simp at congr_coeff{a}{b}{d}{g},
-- exact congr_coeff{a}{b}{d}{g},
end

"""
                    print(string)


def f2():
    f = open("io/out.txt", "r")

    on = False
    for line in f:
        if "congr_coeff" in line:
            if "true" in line:
                continue
            on = True
            a = line[11]
            b = line[12]
            d = line[13]
            g = line[14]
            print(f"""lemma coeff{a}{b}{d}{g} (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :""")
            if len(line) > 20:
                print(line[17:-1])

        elif on:
            if "⊢" in line:
                on = False
                print(f""":=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  have congr_coeff{a}{b}{d}{g}: = congr_arg (coeff (single α {a} + single β {b} + single δ {d} + single γ {g})) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff{a}{b}{d}{g},
  simp at congr_coeff{a}{b}{d}{g},
  -- exact congr_coeff{a}{b}{d}{g},
end

""")
            else:
                l = line[-1]
                l = l.replace("⇑", "")
                l = l.replace("↑x", "(x : ℕ)")
                l = l.replace("↑i", "(i : ℕ)")
                print(line[:-1])


f2()
