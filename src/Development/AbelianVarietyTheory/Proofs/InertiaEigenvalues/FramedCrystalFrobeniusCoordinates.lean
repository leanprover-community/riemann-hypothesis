module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem coord_of_frac_rel {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {d : ℕ}
    (b : Module.Basis (Fin d) A N) (b' : Fin d → N) (hb : ∀ i, b i = b' i) (T c : A) (v w : Fin d → A) (n : N) (r s j k : ℕ)
    (h1 : (T * T) ^ r • (T ^ j • ∑ i, v i • b' i - T ^ k • n) = 0)
    (h2 : T ^ s • (c • n - T ^ j • ∑ i, w i • b' i) = 0) :
    T ^ (r + r + s + j) • (c • v - T ^ k • w) = 0 := by
  obtain rfl : ⇑b = b' := funext hb
  apply b.equivFun.symm.injective
  rw [map_zero, map_smul, map_sub, map_smul, map_smul, Module.Basis.equivFun_symm_apply,
    Module.Basis.equivFun_symm_apply]
  generalize ∑ i, v i • b i = V at *
  generalize ∑ i, w i • b i = W at *
  linear_combination (norm := module) (T ^ s * c) • h1 + (T ^ (r + r + k)) • h2

theorem coord_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)), IsCoord e V → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ r : ℕ, a.f t ^ r • (BK.hf g bk.E ^ S.a • V.v a g m - a.f t ^ k • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) = 0 := by
  intro l _ K bk d S M e hF B V hV t x m k h Q a g
  refine (exists_isFrac (a.f t) (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩ (M.tr a x))).elim fun n hn => hn.elim fun j hn => ?_
  refine (M.Φ_nat a t ⟨a.f t, a.f_I _ t.2⟩ x m k n j h hn).elim fun r hr => ?_
  refine (GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ Q g ⟨a.f t, a.f_I _ t.2⟩ (V.v a g x) n j
    ((congrArg (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩) (hV a g x)).symm.trans hn)).elim fun s hs => ?_
  refine (GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ g.f _ _ (M.tr g) (M.tr_bc g) _ e).elim fun b hb => ?_
  exact ⟨r + r + s + j, coord_of_frac_rel b (fun i => M.tr g (e i)) hb (a.f t) (BK.hf g bk.E ^ S.a)
    (V.v a g m) ((S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) n r s j k
    ((congrArg (fun z => (a.f t * a.f t) ^ r • (a.f t ^ j • z - a.f t ^ k • n)) (hV a g m)).symm.trans hr) hs⟩

end GlobalTheory.BSP
