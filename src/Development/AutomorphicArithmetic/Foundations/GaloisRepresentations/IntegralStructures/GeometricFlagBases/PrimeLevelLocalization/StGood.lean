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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)

namespace UpperTheory.Gal.Int.Geo.Pl

def InIdUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : Plc E) (𝔟 𝔠 : Ideal (𝓞 E)), (∃ s ∈ 𝔠, s ∉ w.asIdeal) →
  ∀ y, InId w (𝔟 * 𝔠) y ↔ InId w 𝔟 y

def ProjLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (_ : Frame S) (N : Lv p) (v : Plc E) (σ : Site S N v) (q' k : ℕ), q'.Prime → q' ≠ σ.q → ∀ K₁ : Subgroup S.G.GAf,
    IsLev S.L (Ideal.span {((ordCompl[σ.q] N.1 * q' ^ k : ℕ) : 𝓞 E)} * σ.𝔞) K₁ → ∀ u ∈ σ.K₀, ∃ x ∈ S.L.KN N.1, x⁻¹ * u ∈ K₁

end UpperTheory.Gal.Int.Geo.Pl

end
