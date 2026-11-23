module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKRealConj

theorem soLoc_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl (F := F)}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.SoLoc ψ t = G.M'.SoLoc ψ t := by
  ext φ
  simp only [Model.SoLoc, Model.IsLinBar, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩

theorem so_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl (F := F)}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.So ψ t = G.M'.So ψ t := by
  unfold Model.So
  rw [soLoc_reG']
  rfl

end GlobalTheory.ThKRealConj
