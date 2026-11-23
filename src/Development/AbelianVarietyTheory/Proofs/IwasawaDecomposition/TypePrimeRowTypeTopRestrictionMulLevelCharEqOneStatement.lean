module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeRowTypeTopRestrictionMulLevelCharEqOne
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.typePrime_rowType_topRestriction_mul_levelChar_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs})
    (h0 : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hh0 : h0 ∈ (rowTyG Ch (rPsymF Ch) w).H)
    (g g' : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    g' ∈ Formalism.L2.Col.GLint X.E (R.N R.m) w.1 →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (g' x) =
      ((diagEmb (𝓞 X.E ⧸ w.1.asIdeal) (Nat.sub_le (R.N R.m) 1) h0)⁻¹ : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x)) →
    CongE w.1 1 g g' →
    LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap *
      (((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) : X.K) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | exact GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | (intros; apply GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one <;> assumption)
