module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PackExOf

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCx GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo (Integ IsFnL)
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

instance algAt (S : Setup A n p) (w : Plc E) : Algebra S.G.F (w.adicCompletion E) := inferInstanceAs (Algebra E (w.adicCompletion E))

def Spl (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ) : Type := {w : Plc E // IsSplitAt w ∧ (p : 𝓞 E) ∉ w.asIdeal}

abbrev fac {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Spl E p) : Loc S.G.GAf (GL (Fin n) (w.1.adicCompletion E)) :=
  T.at hc w.1 w.2.1 w.2.2

structure Half (q : ℕ) (W : Finset (Spl E p)) : Prop where
  above : ∀ w ∈ W, (q : 𝓞 E) ∈ w.1.asIdeal
  all : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → ∃ w ∈ W, w.1 = u ∨ cj w.1 = u
  apart : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → GlobalTheory.Cong.Apart w.1 w'.1

def AdmCusp : Prop :=
  ∀ (X : Type) [Group X] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ) (Ty : TyLev X (GL (Fin n) k)),
    IsOpen (Ty.J : Set (GL (Fin n) k)) → IsCompact (Ty.J : Set (GL (Fin n) k)) → IsOpen (Ty.ψ.ker : Set Ty.J) →
    (∀ (σ : SmIrr (GL (Fin n) k)) (v : σ.V), v ≠ 0 → (∀ g : Ty.J, σ.ρ g v = ((Ty.ψ g : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) →
    ∀ f, Ty.admitted f → ∀ h : X, Ty.L.pr h = 1 → NoConst fun g => f (Ty.L.loc g * h)

end UpperTheory.Gal.Spc
