import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit

section
namespace GlobalTheory.HTW.Model

def WA : WordData 3 where
  up i := i = 1
  sz i := if i = 2 then 3 else 10000
  b := 10000
  w := 3
  S := 1
  η := 1
  m := 1
  J1 i := if i = 1 then {10001, 0} else if i = 2 then {-4, 1} else {-10000, -1}
  J2 i := if i = 1 then {10001, 0} else if i = 2 then {-4} else {-10000, -1}

instance decThickWA : DecidablePred WA.thick := fun i => by unfold WordData.thick; infer_instance

def WB : WordData 2 where
  up i := i = 1
  sz i := if i = 1 then 5 else 100
  b := 100
  w := 5
  S := 1
  η := 1
  m := 1
  J1 i := if i = 1 then {6, 0} else {-100, 1}
  J2 i := if i = 1 then {6, 0} else {-100, -100, 1}

instance decThickWB : DecidablePred WB.thick := fun i => by unfold WordData.thick; infer_instance

def WC : WordData 2 where
  up i := i = 1
  sz _ := 500
  b := 500
  w := 1
  S := 1
  η := 1
  m := 1
  J1 i := if i = 1 then {501, 0} else {-500, 1}
  J2 i := if i = 1 then {501, 0} else {-500, 1}


end GlobalTheory.HTW.Model
end

section
noncomputable section

namespace GlobalTheory.HTW.Rec.Model

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

instance decThickN {n b η : ℕ} (sz : ZMod n → ℕ) : DecidablePred (ThickN b η sz) := fun i => by
  unfold ThickN; infer_instance

def wordMixed : NWord 2 where
  up i := i = 1
  sz i := if i = 1 then 5 else 100
  b := 100
  w := 5
  S := 1
  η := 1
  m := 1
  Mi i := if i = 1 then 1 else 101
  hi i := if i = 1 then 6 else 1

def wordThick : NWord 2 where
  up i := i = 1
  sz i := if i = 1 then 499 else 500
  b := 499
  w := 2
  S := 1
  η := 1
  m := 1
  Mi i := if i = 1 then 1 else 501
  hi i := if i = 1 then 500 else 1

def cycPowSum {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (a : Fin n → ℤ) :
    ↥(GK K) →* Matrix (Fin n) (Fin n) ↥LL.1 where
  toFun g := Matrix.diagonal fun c => (((cycLL (P.PD K) ↥LL.1 ^ (-a c)) g : (↥LL.1)ˣ) : ↥LL.1)
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, Units.val_mul, Matrix.diagonal_mul_diagonal]



section Input

variable (D : D7) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
  (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1)

end Input

end GlobalTheory.HTW.Rec.Model
end
end
