module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdjointEndPairMemGaugedCurveLogarithms
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.adjointEndPair_mem_gaugedCurveLogarithms : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (M M' : Matrix κ κ C) (s : JJ I g → C), IsEnd X V M M' → (∀ q, V.Ge 0 (s q)) → (∀ q, M'.mulVec (X.u (1 - g) q) = s q • X.u (1 - g) q) → ∀ a ∈ Cv X V g, ((fun i => ∑ j, M i j • a.1 j, fun q => s q • a.2 q) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  first | exact @GlobalTheory.RowLaw.CvEnd.end_mem_Cv | exact GlobalTheory.RowLaw.CvEnd.end_mem_Cv | (intros; apply GlobalTheory.RowLaw.CvEnd.end_mem_Cv <;> assumption)
