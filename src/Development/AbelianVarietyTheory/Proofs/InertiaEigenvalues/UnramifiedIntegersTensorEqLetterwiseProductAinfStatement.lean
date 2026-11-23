module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.unramifiedIntegers_tensor_eq_letterwise_product_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1), Function.Bijective emb → ∃ u : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₐ[↥(OL LL)] RA LL, (∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l, IsTiltOf (c : Om l) m xb → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) → u o = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb) ∧ ∀ (S : Type) [CommRing S] [Algebra ↥(OL LL) S] (f f' : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₐ[↥(OL LL)] S), (∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) → f o = f' o) → f = f' := by
  first | exact @GlobalTheory.UnramIdem.exists_prod_hom | exact GlobalTheory.UnramIdem.exists_prod_hom | (intros; apply GlobalTheory.UnramIdem.exists_prod_hom <;> assumption)
