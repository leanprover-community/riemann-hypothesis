module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrime
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime : ∀ {B : Base} (n : ℕ) (g : GA B n) (p : DecoF B.fields.E n ∅ ∅ ∅), PtOf g p → p.deco.1.N = stdLat B.fields.E n → ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin n), IntAtA (F := B.host.F) P ((g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) ∧ IntAtA (F := B.host.F) P (((g⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
  first | exact @GlobalTheory.ptOf_std_entries_intAtA | exact GlobalTheory.ptOf_std_entries_intAtA | (intros; apply GlobalTheory.ptOf_std_entries_intAtA <;> assumption)
