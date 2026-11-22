module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BaseLatticeIsUnimodular

@[expose] public section

noncomputable section

namespace HcS.BasicNotions

open MeasureTheory Filter Topology Matrix

def UpqT (P Q : ℕ) : Type := HcS.UG.Upq P Q

instance (P Q : ℕ) : Group (UpqT P Q) := inferInstanceAs (Group (HcS.UG.Upq P Q))
instance (P Q : ℕ) : TopologicalSpace (UpqT P Q) :=
  inferInstanceAs (TopologicalSpace (HcS.UG.Upq P Q))
instance (P Q : ℕ) : MeasurableSpace (UpqT P Q) := borel (UpqT P Q)

def UpqT.mat {P Q : ℕ} (g : UpqT P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  let g' : HcS.UG.Upq P Q := g; ((g'.1 : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)

def lieU (P Q : ℕ) : Submodule ℝ (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) where
  carrier := {X | Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * HcS.UG.Jpq P Q + Yᴴ * HcS.UG.Jpq P Q + (HcS.UG.Jpq P Q * X + HcS.UG.Jpq P Q * Y)
        = (Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X) + (Yᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * Y) := by
          abel
      _ = 0 := by rw [hX, hY, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, hX,
      smul_zero]

instance (P Q : ℕ) : MeasurableSpace (lieU P Q) := borel (lieU P Q)

end HcS.BasicNotions
