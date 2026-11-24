module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem exists_ringHom_of_isLieComb {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] (a : OAct O G) {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v)
    (ρ : O → Matrix (Fin n) (Fin n) R) (h : ∀ x j, IsLieComb (fun i => ρ x i j) v (v j ≫ a.act x)) :
    ∃ ρ' : O →+* Matrix (Fin n) (Fin n) R, ∀ x, ρ' x = ρ x := by
  classical
  let B := GlobalTheory.Serre.Lie.basis a hv
  refine ⟨(LinearMap.toMatrixAlgEquiv B).toRingEquiv.toRingHom.comp
    (Module.toModuleEnd R (S := O) (GlobalTheory.Serre.Lie a)), fun x => ?_⟩
  ext i j
  have h1 : IsLieComb (fun i => ρ x i j) (fun k => (B k).hom) (v j ≫ a.act x) := by
    simpa only [B, GlobalTheory.Serre.Lie.hom_basis] using h x j
  rw [GlobalTheory.Serre.Lie.isLieComb_iff] at h1
  have h2 : x • B j = ∑ k, ρ x k j • B k := by
    apply GlobalTheory.Serre.Lie.ext
    rw [GlobalTheory.Serre.Lie.hom_act_smul, ← h1, GlobalTheory.Serre.Lie.hom_basis]
  simp [LinearMap.toMatrixAlgEquiv_apply, h2, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem MChart.exists_ringHom_rho :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
      (M : MChart Y), ∃ ρ' : 𝓞 E →+* Matrix (Fin M.n) (Fin M.n) Γ(Y.X, M.U), ∀ a, ρ' a = M.ρ a := by
  intro E _ _ _ H Dw l Xo c O _ β Y M
  obtain ⟨_, _, _, _, _, hm⟩ :=
    sabPull Out.CubePf.cubePull (spMap (RingHom.id Γ(Y.X, M.U)) ≫ M.hU.fromSpec) Y.t
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp Γ(Y.X, M.U)),
      Nonempty (SABMap t' Y.t (spMap (RingHom.id Γ(Y.X, M.U)) ≫ M.hU.fromSpec)) :=
    ⟨_, ⟨hm.choose⟩⟩
  obtain ⟨v', -, hv', hρ⟩ := M.lie _ (RingHom.id _) t' m
  exact exists_ringHom_of_isLieComb t'.act hv' M.ρ hρ

end GlobalTheory.Reg
