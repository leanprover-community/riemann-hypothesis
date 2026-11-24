module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.imgOne_gcd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ H.condN → g ∣ H.condN → H.imgOne (Nat.gcd f g) = H.imgOne f ⊔ H.imgOne g := by
  intro φ H f g hf hg
  have hgcd : Nat.gcd f g ∣ H.condN := (Nat.gcd_dvd_left f g).trans hf
  apply le_antisymm
  · rintro x hx
    rw [H.mem_imgOne hgcd] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have key := Der.Rd.KK_gcd (N := H.condN) ((H.imgOne f ⊔ H.imgOne g).comap H.art) hf hg
      (fun v hv => Subgroup.mem_sup_left ((H.mem_imgOne hf _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      (fun v hv => Subgroup.mem_sup_right ((H.mem_imgOne hg _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      u (Der.Rd.mem_KK.2 hu)
    exact key
  · exact sup_le (H.imgOne_anti (Nat.gcd_dvd_left f g) hf) (H.imgOne_anti (Nat.gcd_dvd_right f g) hg)
