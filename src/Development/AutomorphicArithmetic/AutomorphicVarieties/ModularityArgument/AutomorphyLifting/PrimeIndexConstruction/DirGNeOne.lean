import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PrOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SumDivHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DirOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Mathlib.Topology.Algebra.ClopenNhdofOne
open UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published

namespace UpperTheory.V.Sd.EG

section Norm

variable {l : ℕ} [hl : Fact l.Prime]


variable (l) in

private def U : Subgroup (Qbar l)ˣ where
  carrier := {u | ‖(u : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have e : ((u * v : (Qbar l)ˣ) : Qbar l) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖_‖ < 1
    rw [e]
    refine small_add ?_ hu
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' {u} hu := by
    have e : (u : Qbar l) * (((u⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(u - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at this
    show ‖_‖ < 1
    rw [this]
    exact hu




end Norm

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]






end Gal


end UpperTheory.V.Sd.EG
