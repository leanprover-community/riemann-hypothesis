module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledPrimeToP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.descendedBundle_kernel_killed_primeToP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (exact GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (intros; apply GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent  <;> assumption)
