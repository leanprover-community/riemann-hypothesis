module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.InhVV

open Semi Inh

variable (S : Scheme.{0}) (T : Over S)

def theta1 (k : ℤ) : ThetaGrp (zeroPolAV S).A (zeroPolAV S).L k T where
  pt := 1
  φ := ⟨fun _ => 1⟩
  isGen := by
    intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]

def oneSec (a : ℤ) (T : Over S) : LB.Sec (LPow (zeroPolAV S).A (zeroPolAV S).L a T) :=
  ⟨fun _ => 1, by
    intro i j
    erw [linComb_triv_g]
    simp only [Units.val_one, map_one]
    exact (_root_.one_mul _).symm⟩

end ReciprocityTheory.ChartRestriction.G.Out.InhVV
