module

public import Formalism.LocalToGlobal.Columns.TiedUpDnLoc
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfDecoratedLatticeSplicedAtPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

theorem _root_.GlobalTheory.T.isPointOf_decoratedLattice_splicedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q Q0 Q1 : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 F)) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (p0 : DecoF E n ST SG Q0) (p1 : DecoF E n ST SG Q1) (q : DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g0 p0 → GlobalTheory.Mem.Col2.IsPtOf hc h p1 → (∀ P ∈ Q, ¬ IsOver v P) → (∀ w ∈ SG, ¬ IsOver v w) → Deco.SameOff ST SG v q.deco.1 p1.deco.1 → (∀ P : HeightOneSpectrum (𝓞 E), IsOver v P → localization₂ P.asIdeal q.deco.1.N = localization₂ P.asIdeal p0.deco.1.N) → (∀ P : ST, IsOver v P.1 → q.deco.1.f P = p0.deco.1.f P) → (∀ P : Q, ∃ P' : Q1, P'.1 = P.1 ∧ p1.fr P' = q.fr P) → GlobalTheory.Mem.Col2.IsPtOf hc (h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0))) q := by
  first | exact @GlobalTheory.Mem.Col2.Splice.isPtOf_splice | exact GlobalTheory.Mem.Col2.Splice.isPtOf_splice | (intros; apply GlobalTheory.Mem.Col2.Splice.isPtOf_splice <;> assumption)
