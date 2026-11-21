import Mathlib

noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyNu.{u_1} :
    {L : Type u_1} → [NormedField L] → Multiset L → ℝ :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦
      (Multiset.map (fun (z : L) ↦ ‖z‖) (Multiset.filter (fun (z : L) ↦ (1 : ℝ) ≤ ‖z‖) R)).prod

noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyF.{u_1} :
    {L : Type u_1} → [inst : NormedField L] → Multiset L → Polynomial L :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦
      (Multiset.map (fun (z : L) ↦ Polynomial.X - (Polynomial.C : L → Polynomial L) z) R).prod

noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyP.{u_1} :
    {L : Type u_1} → [NormedField L] → Multiset L → Multiset L :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦ Multiset.filter (fun (z : L) ↦ ‖z‖ < (1 : ℝ)) R

