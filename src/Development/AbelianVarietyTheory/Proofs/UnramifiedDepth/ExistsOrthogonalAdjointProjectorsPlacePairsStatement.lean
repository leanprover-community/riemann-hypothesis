module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsOrthogonalAdjointProjectorsPlacePairs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_orthogonal_adjoint_projectors_placePairs : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (p : ∀ o, PairData Y d (I o)), (∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' → ∃ a : O, V.v ((p x.1).em x.2.1 x.2.2 a - (p x'.1).em x'.2.1 x'.2.2 a) = 0) → ∃ M : Orb → Fin 2 → Matrix (Fin dd) (Fin dd) C, (∀ o, IsEnd (Y.raw (p o)) V (M o 0) (M o 1) ∧ IsEnd (Y.raw (p o)) V (M o 1) (M o 0)) ∧ (∀ o g c, (M o g).mulVec ((p o).u g c) = (p o).u g c) ∧ (∀ o g o' g' c, (o, g) ≠ (o', g') → (M o g).mulVec ((p o').u g' c) = 0) ∧ ∀ o g v, ∃ b : I o g → C, (M o g).mulVec v = ∑ c, b c • (p o).u g c := by
  first | exact @GlobalTheory.PlaceProj.exists_orth_proj | exact GlobalTheory.PlaceProj.exists_orth_proj | (intros; apply GlobalTheory.PlaceProj.exists_orth_proj <;> assumption)
