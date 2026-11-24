module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

def EvEx : Prop := ∀ (p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] (T : AdT p E) (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal →
  ∃ ev : AfP p ⊗[ℚ] E →+* w.adicCompletion E, ∀ x, ev (T.Φ x) = pLoc E w x

def VecCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ vec : ∀ w : Plc E, AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E),
  (∀ v, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → vec w v = 0) → v = 0) ∧
  (∀ v, v ∈ LaHat S.D ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i, vec w v i ∈ w.adicCompletionIntegers E) ∧
  (∀ y : ∀ w : Plc E, Fin n → w.adicCompletion E, (∀ w i, y w i ∈ w.adicCompletionIntegers E) →
    ∃ v, ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → vec w v = y w) ∧
  (∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ (y : Fin n → 𝓞 E) i, vec w (inAf S.D y) i = algebraMap (𝓞 E) _ (y i)) ∧
  (∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ g v, vec w (S.L.actG (T.j g) v) =
    (GeneralLinearGroup.map (pLoc E w) T.a * comp w g * (GeneralLinearGroup.map (pLoc E w) T.a)⁻¹).val *ᵥ vec w v) ∧
  ∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ (c : 𝓞 E) v,
    vec w (UpperTheory.Gal.Int.Geo.mulF S.D c v) = algebraMap (𝓞 E) (w.adicCompletion E) c • vec w v

def StdForm2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ (B : DForm S.G) (x : (AfP p ⊗[ℚ] S.G.C)ˣ) (hx : Triv S.G (AfP p) B.β x 1),
    (∀ y : GL (Fin n) E × ℚˣ, y ∈ GlobalTheory.LKCx.grp S.G B.β ↔ y ∈ Gam0 E n) ∧
    ∀ (y : GL (Fin n) E × ℚˣ) (h : y ∈ GlobalTheory.LKCx.grp S.G B.β) (h' : y ∈ Gam0 E n), (B.embAt x 1 hx ⟨y, h⟩).1 = T.j (rat ⟨y, h'⟩)

def PIntRev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (y : Gam0 E n), (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ KGL w (n := n)) →
    inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G

def IntCof : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (a : GL (Fin n) (Af E)),
  ∀ᶠ w in Filter.cofinite, GeneralLinearGroup.map (pLoc E w) a ∈ KGL w (n := n)

end UpperTheory.Gal.W2.Seed
