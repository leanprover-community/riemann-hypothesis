module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairLeIffPairHtLe

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem colMatchAll : ColMatchAll := by
  intro B X I h hX l Z hJ u a
  have KO := GlobalTheory.Mem.Col2.KerRat.kernelsOver_of_family I l Z h hJ (GlobalTheory.Core.Ht2.family_laws I h hX l Z) u a
  refine ⟨?_, fun c x φ F z hx hF => ?_⟩
  · obtain ⟨⟨b⟩, hb⟩ := KO.period
    obtain ⟨hY, hK, hF, -, -⟩ := hb b
    exact ⟨⟨b, hY, hK, hF⟩⟩
  · obtain ⟨hY, hK, hF', hM, heq⟩ := KO.period.2 c.b
    have ex : x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ := Subtype.ext (funext hx)
    have eF : F = GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a z := by
      apply Subtype.ext; funext t p; exact hF p
    subst ex; subst eF
    rw [heq φ z]
    rfl

end GlobalTheory.Core.Ht2

end
