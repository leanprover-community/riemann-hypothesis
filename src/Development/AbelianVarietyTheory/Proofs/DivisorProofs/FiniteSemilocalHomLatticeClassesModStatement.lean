module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSemilocalHomLatticeClassesMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.finite_semilocal_hom_lattice_classes_mod : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E L → Submodule.IsLattice E L' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ∧ Nat.card (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ≤ (cA * c) ^ (Module.finrank ℚ E * a * b) := by
  first | exact @GlobalTheory.SemilocalClasses.finite_card_classes | exact GlobalTheory.SemilocalClasses.finite_card_classes | (intros; apply GlobalTheory.SemilocalClasses.finite_card_classes <;> assumption)
