import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs

#check div_mul_cancel

namespace Zalaegerszegi
variable (x y z : ℝ )


theorem feladat(h0: x≠y)(h1: x≠ 1)(h2: y ≠ 1)(h3: (y * z - x ^ 2) / (1 - x) = (x * z - y ^ 2) / (1 - y)) :(y * z - x ^ 2 )/ (1 - x)= (x + y + z):= by
  have h1ex: (1-x)≠0:= by exact sub_ne_zero_of_ne (id (Ne.symm h1))
  have h2ex: (1-y)≠0:= by exact sub_ne_zero_of_ne (id (Ne.symm h2))
  have h0ex: (x-y)≠0:= by exact sub_ne_zero_of_ne h0

  have new_goal: ((y * z) - x ^ 2) / (1-x) = x + y + z ↔ (x + y - 1) * z = x + y - x * y := by
    calc
      ((y * z) - x ^ 2) / (1-x) = x + y + z ↔ (((y * z) - x ^ 2) / (1-x))*(1-x) = (x + y + z)*(1-x) := by
        exact Iff.symm (mul_left_inj' h1ex)
      _↔((y * z) - x ^ 2)=(x + y + z)*(1-x) :=by
        refine Iff.symm (Eq.congr ?h₁ rfl)
        exact Eq.symm (div_mul_cancel₀ (y * z - x ^ 2) h1ex)
      _↔ y * z - x ^ 2 = x + y + z - x ^ 2 - x * y - z * x := by
        apply Eq.congr_right
        rw[mul_sub, mul_one, add_mul, add_mul, pow_two, ← sub_sub, ← sub_sub]
        simp[add_assoc,mul_comm]
      _ ↔ y * z - x ^ 2 + (x ^ 2 + z * x - z) = x + y + z - x ^ 2 - x * y - z * x + (x ^ 2 + z * x - z) := by
        exact Iff.symm add_right_cancel_iff
      _↔ y * z + x * z - z = x + y - x * y := by
        repeat rw[add_sub]
        ring_nf
      _↔ (x + y - 1) * z = x + y - x * y:= by
        apply Eq.congr_left
        rw[← add_mul]
        nth_rewrite 2 [←  one_mul z]
        rw[← sub_mul, add_comm]


  rw[new_goal]

  have h3_re: (y * z - x ^ 2) / (1 - x) = (x * z - y ^ 2) / (1 - y) ↔ (x + y -1) * z = x + y - x * y  :=by
    calc
       (y * z - x ^ 2) / (1 - x) = (x * z - y ^ 2) / (1 - y) ↔ (y * z - x ^ 2) / (1 - x)*(1 - x) = (x * z - y ^ 2) / (1 - y)*(1 - x) := by
          exact Iff.symm (mul_left_inj' h1ex)
       _↔  (y * z - x ^ 2) = (x * z - y ^ 2) / (1 - y)*(1 - x):=by
          refine Iff.symm (Eq.congr ?h₁ rfl)
       _↔ (y * z - x ^ 2)*(1 - y) = (x * z - y ^ 2) / (1 - y) * (1 - x) * (1 - y):=by
          exact Iff.symm (mul_left_inj' h2ex)
       _↔  (y * z - x ^ 2)*(1 - y) = (x * z - y ^ 2) * (1 - x):= by
          apply Eq.congr_right
          rw[mul_assoc, mul_comm (1 - x), ← mul_assoc, div_mul_cancel₀ (x * z - y ^ 2) h2ex]
       _↔  (y * z - x ^ 2)*(1 - y) + (- x * z + y ^ 2 + x ^ 2 * z - y ^ 2 * x) = (x * z - y ^ 2) * (1 - x) + (- x * z + y ^ 2 + x ^ 2 * z - y ^ 2 * x):=by
          exact Iff.symm add_right_cancel_iff
       _↔  y * z - x ^ 2 - y ^ 2 * z + x ^ 2 * y - x * z + y ^ 2 + x ^ 2 * z - y ^ 2 * x = 0:=by
          ring_nf
       _↔  y * z - x ^ 2 - y ^ 2 * z + x ^ 2 * y - x * z + y ^ 2 + x ^ 2 * z - y ^ 2 * x + (x ^ 3 - y ^ 3) = 0 + (x ^ 3 - y ^ 3):=by
          exact Iff.symm add_right_cancel_iff
       _↔ (y - x - y  ^ 2 + x ^ 2)*(z + y + x) = x  ^ 3 - y ^ 3 := by
          apply Eq.congr
          · ring
          · ring
       _↔ (x - y)*((x + y - 1)*(z + y + x))=(x - y)*(x ^ 2 + x * y + y  ^ 2):=by --kihagyható lépés az olvashatóság a cél
         apply Eq.congr
         · ring
         · ring
       _↔  (x + y - 1)*(z + y + x) = (x ^ 2 + x * y + y  ^ 2)  :=by
         rw[mul_right_inj' h0ex]
       _↔  (x + y - 1)*(z + y + x)-(x + y)*(x + y - 1) = (x ^ 2 + x * y + y  ^ 2) - (x + y)*(x + y - 1)  :=by
         exact Iff.symm add_right_cancel_iff
       _↔  (x + y -1) * z = x + y - x * y :=by
        ring_nf


  apply h3_re.mp h3 --modus ponens ekvivalencia ↔ előre fele


#check feladat
end Zalaegerszegi
