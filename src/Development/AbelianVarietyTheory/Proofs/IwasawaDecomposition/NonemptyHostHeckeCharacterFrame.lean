module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveCharacterOfIsCyclic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAlStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHostStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExistsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExistsStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory

theorem nonempty_hFrame : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ), (∀ k, SplitsC H.E (H.g k)) → SplitsC H.E H.pde → SplitsC H.E H.pde' → (∀ j τ, ∃ z : ℤ, e j τ = z) → (∀ j, UpperTheory.MUQ (embPsi H) (e j)) → Nonempty (HFrame H e) := by
  intro R H e hg hp hp' he hs
  obtain ⟨⟨P⟩, ⟨W⟩⟩ := GlobalTheory.nonempty_piBar_and_omg R H
  have hmu : ∀ j : Fin R.m, ∃ χ : HChar H.E, IsMu0 P W (e j) j.1 χ := fun j =>
    GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ R H P W (e j) j.1 hg (he j) (hs j)
  choose mu hmu using hmu
  obtain ⟨eta, heta⟩ := GlobalTheory.T.host_etaTilde_character_exists R H
  obtain ⟨chi, hchi⟩ := GlobalTheory.T.exists_unramified_cmType_heckeChar_on_host R H
  obtain ⟨d, hd⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde H.pde_prime H.pde_mod.1 hp
  obtain ⟨d', hd'⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde' H.pde'_prime H.pde_mod.2 hp'
  exact ⟨⟨P, W, mu, eta, chi, d, d', hmu, heta, hchi, hd, hd'⟩⟩

end GlobalTheory
