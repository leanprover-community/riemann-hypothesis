import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import BuildAid.ForwardExisting

section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj

namespace GlobalTheory.AbelianLetters

theorem scale_tangent_pow (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (n : ℕ) (hn : 0 < n) (hv : IsTangent v) :
    spMap (epsScaleR ((n : ℂ)⁻¹)) ≫ (v ^ n).left = v.left := by
  have h : GrpTangent.epsScale ((n : ℂ)⁻¹) ≫ (v ^ n) = v := by
    rw [GrpTangent.pow_eq_epsScale_comp hv, GrpTangent.epsScale_mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'),
      GrpTangent.epsScale_one, Category.id_comp]
  exact congrArg (fun φ => φ.left) h

end GlobalTheory.AbelianLetters
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_pow_scale_inv_eq : ∀ (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (n : ℕ), 0 < n → IsTangent v → spMap (epsScaleR ((n : ℂ)⁻¹)) ≫ (v ^ n).left = v.left := by
  atlas_forward_decl GlobalTheory.AbelianLetters.scale_tangent_pow
