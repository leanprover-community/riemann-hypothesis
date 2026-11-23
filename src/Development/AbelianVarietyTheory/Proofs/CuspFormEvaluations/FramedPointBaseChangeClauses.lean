module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrBCField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBaseChangeEigenBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

namespace GlobalTheory

theorem framedPoint_bcGenR (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) : BcGenRSt Xo c := by
  intro p T _ _ ψ y
  obtain ⟨z, hx, -, pm, h1, h2, h3⟩ :=
    GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c p.R T ψ y
  obtain ⟨x, _, _, _, _, _, s, gen⟩ := z
  dsimp only at hx pm h1 h2 h3
  subst hx
  have hpm : pm = bcPm ψ.toRingHom y.x := by
    apply pullback.hom_ext
    · exact h2.trans (bcPm_fst _ _).symm
    · exact h1.trans (bcPm_snd _ _).symm
  subst hpm
  exact ⟨s, h3, gen⟩

theorem framedPoint_baseChange_clauses :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), BcLieAnySt Xo c ∧ BcLieRSt Xo c ∧ BcGenRSt Xo c ∧ FrBCFieldSt Xo c := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨?_, ?_, framedPoint_bcGenR E H Dw l Xo c, ?_⟩
  · intro S _ _ K _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c S K ψ y τ w hw he
  · intro p T _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c p.R T ψ y τ w hw he
  · intro S _ _ y K _ _ ψ
    exact GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c S K ψ y

end GlobalTheory
