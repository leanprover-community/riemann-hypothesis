module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIffRead
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetReductionFixedIffResidues
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.couplingCoset_reduction_fixed_iff_residues : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, j + 1 = R.m → ∀ (p p' : PtAt R sel mu cst u j) (h : GLG (E := X.E) (n := R.N j) (SG := Pr.vGs)), p'.1.1 = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 → p'.1.2 = p.1.2 → ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → (cosetIn p' P = cosetIn p P ↔ ((h ⟨P.1, hP⟩ : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) *ᵥ GlobalTheory.Mem.Col2.TypeRead.cvec p P = GlobalTheory.Mem.Col2.TypeRead.cvec p P) := by
  exact @GlobalTheory.Mem.Col2.TypeRead.cosetIn_smul_eq_iff
