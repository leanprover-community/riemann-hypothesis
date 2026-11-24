module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
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
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.dual_lattice_local_characterization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat (dualL cm.sig J L) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F), x ∈ loc v (dualL cm.sig J L) ↔ ∀ z ∈ loc v L, hR cm.sig J (v.adicCompletion F) z x ∈ intV E v) ∧ ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F (dualL cm.sig J L) ↔ ∀ z ∈ hat F L, hR cm.sig J (Ad F) z x ∈ OAd F E := by
  first | exact @GlobalTheory.St.G.dualL_local_adelic | exact GlobalTheory.St.G.dualL_local_adelic | (intros; apply GlobalTheory.St.G.dualL_local_adelic <;> assumption)
