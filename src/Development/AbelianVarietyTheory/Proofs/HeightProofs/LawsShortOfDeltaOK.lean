module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SameSpaceOfLawsJ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin

theorem laws_short_of_deltaOK : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → 0 ∉ D.host.levelPrimes → ∀ (p : ℕ) (I : Ideal (𝓞 D.host.E)), (p = D.host.pde ∨ p = D.host.pde') → ∀ dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n, (∀ j, InR D j → ∀ n, DeltaOK (dd j n) p I) → LawsP ({ T with dδ := dd } : Top D) ∧ LawsSh ({ T with dδ := dd } : Top D) := by
  intro D J T hJ h hT h0 p I hp dd hd
  have h' : LawsP ({ T with dδ := dd } : Top D) := { h with }
  have hb : 0 < badN D := by
    have := D.host.qd_big
    unfold badN
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega))
      (Finset.prod_pos fun x hx => Nat.pos_of_ne_zero fun h => h0 (h ▸ hx))
  refine ⟨h', GlobalTheory.ShortLaws.lawsSh_of_pinned GlobalTheory.chartIndependence_unconditional _ h' hb
    (GlobalTheory.ShortLaws.sameSpace_of_lawsJ J T hJ hT) p hp fun j hj n => ?_⟩
  obtain ⟨⟨h1, -, h3, h4, h5⟩, ⟨h6, h7⟩, h8⟩ := hd j hj n
  exact ⟨h1, h3, h4, h5, h6, h7, h8⟩

end GlobalTheory.FinalJoin
