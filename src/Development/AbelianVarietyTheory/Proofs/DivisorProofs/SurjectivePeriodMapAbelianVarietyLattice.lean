module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFrameLogDerivativeQuasiPeriodicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechClassOfQuasiPeriodicHolomorphicCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSubPiHermitianOfLatticeAddHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerSurj

theorem isPer_transport {A : Over (Sp ℂ)} {g : ℕ} (ex₀ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A))
    (Λ₀ : Submodule ℤ (Fin g → ℂ))
    (h₀ : ∀ p : Λ₀ →+ ℂ, ∃ x, IsPer ex₀ Λ₀ x p) :
    ∀ (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Λ : Submodule ℤ (Fin g → ℂ)),
      ex = ex₀ → Λ = Λ₀ → ∀ p : Λ →+ ℂ, ∃ x, IsPer ex Λ x p := by
  intro ex Λ hex hΛ
  subst hex hΛ
  exact h₀

theorem surj_of_isAH (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (M : LB A.left) (u : HolUnif A M g)
    (hA : IsAbelianScheme A) (hM : M.IsLB) (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hAH : u.IsAH H χ) :
    ∀ p : u.Λ →+ ℂ, ∃ x, IsPer u.ex u.Λ x p := by
  intro p
  obtain ⟨f, v, hfv⟩ := GlobalTheory.T.exists_linear_sub_pi_hermitian_of_lattice_addHom g u.Λ H u.discrete u.full hAH.2.1 p
  obtain ⟨hd, hr, hq⟩ := GlobalTheory.T.appell_humbert_frame_log_derivative_quasi_periodic A g M u hA hM H χ hAH v
  refine GlobalTheory.T.exists_cechClass_of_quasiPeriodic_holomorphic_cover A g M u hA M.ι M.U
    (fun i z => f z + fderiv ℂ (u.fr i) z v / u.fr i z) p hM.cover ?_ ?_ ?_
  · intro i
    exact f.differentiable.differentiableOn.add (hd i)
  · intro i j
    have : ((fun z => f z + fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => f z + fderiv ℂ (u.fr j) z v / u.fr j z) =
        ((fun z => fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => fderiv ℂ (u.fr j) z v / u.fr j z) := by
      funext z; simp only [Pi.sub_apply]; ring
    rw [this]; exact hr i j
  · intro i l z hz
    rw [hq i l z hz, map_add (f := _), hfv l]
    ring

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ p : u.Λ →+ ℂ, ∃ x, IsPer u.ex u.Λ x p := by
  intro A _ g L u hA
  obtain ⟨M, u', H, χ, hM, hex, hΛ, hAH⟩ := GlobalTheory.AHExists.exists_isAH A g hA L u
  exact isPer_transport u'.ex u'.Λ (surj_of_isAH A g M u' hA hM H χ hAH) u.ex u.Λ hex.symm hΛ.symm

end GlobalTheory.PerSurj
