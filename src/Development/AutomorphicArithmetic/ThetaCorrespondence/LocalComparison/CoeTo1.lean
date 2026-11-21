import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonFromAlternative

section
theorem UpperTheory.Lit.Cmp.locTied_of6 : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied6 l P AI) → Nonempty (Formalism.BasicNotions.LocTied l P AI) :=
  Formalism.BasicNotions.CmpTie.local_comparison_from_alternative
end

section
noncomputable section

open Formalism.BasicNotions

def Formalism.BasicNotions.LocTied.to6 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) : LocTied6 l P AI :=
  Classical.choice (UpperTheory.Lit.Cmp.locTied6 l P AI ⟨T⟩)

def Formalism.BasicNotions.LocTied6.to1 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : LocTied l P AI :=
  Classical.choice (UpperTheory.Lit.Cmp.locTied_of6 l P AI ⟨T⟩)

instance UpperTheory.Lit.Cmp.coeTo6 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} :
    CoeTail (LocTied l P AI) (LocTied6 l P AI) := ⟨LocTied.to6⟩

instance UpperTheory.Lit.Cmp.coeTo1 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} :
    CoeTail (LocTied6 l P AI) (LocTied l P AI) := ⟨LocTied6.to1⟩

end
end
