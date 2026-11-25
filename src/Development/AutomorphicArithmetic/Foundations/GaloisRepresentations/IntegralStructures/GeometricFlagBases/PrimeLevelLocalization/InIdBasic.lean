module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

def Near1 {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E) (e : ℕ) (g : GLw n w) : Prop :=
  ∀ i k, InId w (w.asIdeal ^ e) ((g.val - 1) i k)

def NearNbhd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Plc E) (O : Set (GLw n w)), IsOpen O → 1 ∈ O →
    ∃ e : ℕ, ∀ e', e ≤ e' → ∀ g ∈ KGL w (n := n), Near1 w e' g → g ∈ O

def StabOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S)
    (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    Off V p → ∃ (T : Finset (Plc E)) (e : ℕ), (∀ u ∈ T, (p : 𝓞 E) ∉ u.asIdeal ∧ (u ∈ V.S ∨ F.a u ∉ KGL u (n := n))) ∧
      ∀ k' : GUf E n, F.j k' ∈ S.L.KN 1 → (∀ u ∈ T, Near1 u e (F.a u * comp u k' * (F.a u)⁻¹)) → Stab F V (F.j k')

end UpperTheory.Gal.Int.Geo.Pl
