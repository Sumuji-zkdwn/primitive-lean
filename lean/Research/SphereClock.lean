import Elastica.Geometry
import Mathlib.Tactic

/-!
# Sphere clock, finite proof model

A reconstructed Elastica circle is swept into a sphere. The moving needle
is a whole longitude meridian, and the dial is its cumulative visit count.
This does not assert a Dirac distribution, rational-angle gluing, or holonomy.
-/

namespace SphereClock

noncomputable section

def meridianAngle : ℝ → ℝ := fun s => (0 : ℝ) + 1 * s

theorem meridian_x (s : ℝ) :
    Elastica.xCoord meridianAngle 0 s = Real.sin s := by
  simpa [meridianAngle] using
    (Elastica.xCoord_affine (0 : ℝ) 1 0 s (by norm_num))

theorem meridian_z (s : ℝ) :
    Elastica.yCoord meridianAngle 0 s = 1 - Real.cos s := by
  simpa [meridianAngle] using
    (Elastica.yCoord_affine (0 : ℝ) 1 0 s (by norm_num))

def sphereX (s a : ℝ) : ℝ :=
  Elastica.xCoord meridianAngle 0 s * Real.cos a

def sphereY (s a : ℝ) : ℝ :=
  Elastica.xCoord meridianAngle 0 s * Real.sin a

def sphereZ (s : ℝ) : ℝ :=
  Elastica.yCoord meridianAngle 0 s - 1

theorem on_unit_sphere (s a : ℝ) :
    sphereX s a ^ 2 + sphereY s a ^ 2 + sphereZ s ^ 2 = 1 := by
  change
    (Elastica.xCoord meridianAngle 0 s * Real.cos a) ^ 2 +
    (Elastica.xCoord meridianAngle 0 s * Real.sin a) ^ 2 +
    (Elastica.yCoord meridianAngle 0 s - 1) ^ 2 = 1
  rw [meridian_x, meridian_z]
  calc
    (Real.sin s * Real.cos a) ^ 2 +
        (Real.sin s * Real.sin a) ^ 2 +
        (1 - Real.cos s - 1) ^ 2 =
      (Real.sin s) ^ 2 * ((Real.cos a) ^ 2 + (Real.sin a) ^ 2) +
        (Real.cos s) ^ 2 := by ring
    _ = (Real.sin s) ^ 2 + (Real.cos s) ^ 2 := by
      rw [Real.cos_sq_add_sin_sq]
      ring
    _ = 1 := Real.sin_sq_add_cos_sq s

end

/-! Exact discrete time derivative of the clock dial. -/

def needle {α : Type*} [DecidableEq α]
    (route : ℕ → α) (t : ℕ) (p : α) : ℕ :=
  if route t = p then 1 else 0

def dial {α : Type*} [DecidableEq α]
    (route : ℕ → α) : ℕ → α → ℕ
  | 0, _ => 0
  | Nat.succ t, p => dial route t p + needle route t p

@[simp] theorem dial_zero {α : Type*} [DecidableEq α]
    (route : ℕ → α) (p : α) : dial route 0 p = 0 := rfl

theorem dial_step {α : Type*} [DecidableEq α]
    (route : ℕ → α) (t : ℕ) (p : α) :
    dial route (t + 1) p = dial route t p + needle route t p := rfl

theorem needle_eq_dial_diff {α : Type*} [DecidableEq α]
    (route : ℕ → α) (t : ℕ) (p : α) :
    needle route t p = dial route (t + 1) p - dial route t p := by
  rw [dial_step]
  omega

theorem full_history_determines_needle {α : Type*} [DecidableEq α]
    (u v : ℕ → α) (h : ∀ t p, dial u t p = dial v t p)
    (t : ℕ) (p : α) :
    needle u t p = needle v t p := by
  calc
    needle u t p = dial u (t + 1) p - dial u t p :=
      needle_eq_dial_diff u t p
    _ = dial v (t + 1) p - dial v t p := by
      rw [h (t + 1) p, h t p]
    _ = needle v t p := (needle_eq_dial_diff v t p).symm

theorem full_history_determines_route {α : Type*} [DecidableEq α]
    (u v : ℕ → α) (h : ∀ t p, dial u t p = dial v t p) :
    u = v := by
  funext t
  have hneedle := full_history_determines_needle u v h t (u t)
  have hone : needle v t (u t) = 1 := by
    calc
      needle v t (u t) = needle u t (u t) := hneedle.symm
      _ = 1 := by simp [needle]
  by_contra hne
  have hne' : v t ≠ u t := fun he => hne he.symm
  simp [needle, hne'] at hone

/-! A needle covers all sampled latitudes at one longitude. -/

abbrev SurfaceSample (lat lon : ℕ) := Fin lat × Fin lon

def meridianNeedle {lat lon : ℕ} (route : ℕ → Fin lon)
    (t : ℕ) (p : SurfaceSample lat lon) : ℕ :=
  needle route t p.2

def surfaceDial {lat lon : ℕ} (route : ℕ → Fin lon)
    (t : ℕ) (p : SurfaceSample lat lon) : ℕ :=
  dial route t p.2

theorem meridian_is_surface_difference {lat lon : ℕ}
    (route : ℕ → Fin lon) (t : ℕ) (p : SurfaceSample lat lon) :
    meridianNeedle route t p =
      surfaceDial route (t + 1) p - surfaceDial route t p :=
  needle_eq_dial_diff route t p.2

/-! The final dial can forget visit order. -/

def routeAB : ℕ → Bool
  | 0 => false
  | 1 => true
  | _ => false

def routeBA : ℕ → Bool
  | 0 => true
  | 1 => false
  | _ => false

theorem same_final_dial : dial routeAB 2 = dial routeBA 2 := by
  funext b
  cases b <;> decide

theorem different_first_needle :
    needle routeAB 0 false ≠ needle routeBA 0 false := by
  decide

theorem final_dial_forgets_order :
    dial routeAB 2 = dial routeBA 2 ∧ routeAB ≠ routeBA := by
  constructor
  · exact same_final_dial
  · intro h
    have hzero := congrFun h 0
    simp [routeAB, routeBA] at hzero

#print axioms meridian_x
#print axioms on_unit_sphere
#print axioms needle_eq_dial_diff
#print axioms full_history_determines_route
#print axioms final_dial_forgets_order

end SphereClock
