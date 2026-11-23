module

public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.MemClosureOfMemSS
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lam {k : ℕ} (L : Submodule (SS F E) (Fin k → AE F E)) : Submodule (𝓞 E) (Fin k → E) where
  carrier := {x | (fun i => inclE (F := F) (AF F) (x i)) ∈ L}
  add_mem' := by
    intro a b ha hb
    have h : (fun i => inclE (F := F) (AF F) ((a + b) i)) =
        (fun i => inclE (F := F) (AF F) (a i)) + (fun i => inclE (F := F) (AF F) (b i)) := by
      funext i; simp
    show (fun i => inclE (F := F) (AF F) ((a + b) i)) ∈ L
    rw [h]
    exact L.add_mem ha hb
  zero_mem' := by
    have h : (fun i => inclE (F := F) (AF F) ((0 : Fin k → E) i)) = 0 := by
      funext i; simp
    show (fun i => inclE (F := F) (AF F) ((0 : Fin k → E) i)) ∈ L
    rw [h]
    exact L.zero_mem
  smul_mem' := by
    intro r x hx
    have h : (fun i => inclE (F := F) (AF F) ((r • x) i)) =
        (⟨inclE (F := F) (AF F) (r : E), incl_mem_SS ⟨r, rfl⟩⟩ : SS F E) •
          (fun i => inclE (F := F) (AF F) (x i)) := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
    show (fun i => inclE (F := F) (AF F) ((r • x) i)) ∈ L
    rw [h]
    exact L.smul_mem _ hx

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
