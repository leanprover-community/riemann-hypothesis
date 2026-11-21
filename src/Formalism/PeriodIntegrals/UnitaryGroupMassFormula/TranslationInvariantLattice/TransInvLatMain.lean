import Formalism.PeriodIntegrals.TransInvLat
import Formalism.PeriodIntegrals.AreaLat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat

section
open Classical Complex

namespace PI.TransInvLatW

theorem shift_core (P A : ℂ) (G : ℂ → ℂ) (x y X Y : ℂ)
    (hy : ∀ z, G (z + y) * exp (-P * z * Y / A - P * y * Y / (2 * A)) = G z)
    (hph : exp (P * (x * Y - y * X) / (2 * A)) = 1) (z : ℂ) :
    G (z + (x + y)) * exp (-P * z * (X + Y) / A - P * (x + y) * (X + Y) / (2 * A)) =
      G (z + x) * exp (-P * z * X / A - P * x * X / (2 * A)) := by
  have h1 := hy (z + x)
  have hz : z + (x + y) = z + x + y := by ring
  rw [hz, ← h1, mul_assoc (G (z + x + y)), ← Complex.exp_add]
  congr 1
  have hE : -P * z * (X + Y) / A - P * (x + y) * (X + Y) / (2 * A) =
      (-P * (z + x) * Y / A - P * y * Y / (2 * A) + (-P * z * X / A - P * x * X / (2 * A))) +
        P * (x * Y - y * X) / (2 * A) := by ring
  rw [hE, Complex.exp_add, hph, mul_one]

def PhaseOne : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∀ (x ω : ℂ) (m : ℕ), 0 < m →
    (m : ℂ) * (x / 2) ∈ lat2 w₁ w₂ → ω ∈ lat2 w₁ w₂ →
      exp ((Real.pi : ℂ) * (x * (starRingEnd ℂ) (2 * (m : ℂ) * ω) -
        (2 * (m : ℂ) * ω) * (starRingEnd ℂ) x) / (2 * (area (lat2 w₁ w₂) : ℂ))) = 1


end PI.TransInvLatW
end

section
open Classical Complex

namespace PI.TransInvLatW



end PI.TransInvLatW
end
