import data.real.basic

-- example (a b c : ℝ) : a * c + b * c = 0 :=
-- begin
--   ring_nf, -- c * a + b * c = 0
--   ring_nf, -- (a + b) * c = 0
--   ring_nf, -- c * a + c * b = 0
-- end

-- have : a * b * d * c = a * b * c * d := by ring_nf,
-- rw this

example (a b : ℝ) (h : a + b = 0) : a = -b := 
begin
  
  fail_if_success
end

