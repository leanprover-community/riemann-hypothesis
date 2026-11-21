import Mathlib
import Formalism.UnipotentAdelicQuotients.CyclicNormPrinciple

open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory.CyclicNormCheck



theorem norm_of_root {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] {a r : K} (h : r ^ Module.finrank F E = a) :
    ∃ y : K ⊗[F] E, Algebra.norm K y = a :=
  ⟨algebraMap K _ r, by rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h]⟩











end GlobalTheory.CyclicNormCheck
