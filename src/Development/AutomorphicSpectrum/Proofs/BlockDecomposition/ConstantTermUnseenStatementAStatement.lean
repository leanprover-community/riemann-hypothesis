module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.constant_term_unseen_statement_a : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∃ T : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GA E (r + s), ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E)) (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ T ∧ l ∈ L ∧ g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets | exact GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets | (intros; apply GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets <;> assumption)
