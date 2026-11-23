module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefClassDecompIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassRestObj

theorem defClassRest : ∀ D : D7, DefClassRest D := by
  intro D W hW hsig
  obtain ⟨⟨θ, hθ⟩, A, hA⟩ := GlobalTheory.DecompCompare.exists_data D W hW hsig
  have hK : KSub D W W.rank 0 θ A = StabFin.SFin D.sp.cm.sig W.gram (L0c D W) :=
    SetLike.coe_injective (StabFin.KSub_eq D W hW hsig θ hθ A hA)
  obtain ⟨-, n, g, hcov, hdisj, -, hsum⟩ := GlobalTheory.DefiniteDecompObj.doubleCosets_mass D W hW hsig θ hθ A hA
  rw [hK] at hcov hdisj hsum
  exact ⟨n, g, hcov, hdisj, hsum⟩

end GlobalTheory.ClassRestObj
