import NumberTheory.Notations
import NumberTheory.Theorems


-- раскрываем по моему определению (есть в Notations.lean)
-- нам нужно доказать:
-- n делится на 1
-- n+1 делится на 1
-- мы можем найти целые x,y для nx + y*(n+1) = 1

-- первые два условия тривиальны (теорема для этого доказана в файле NumberTheory/Theorems)
-- one_dvd' закрывает первые два условия

-- коэффиценты для 3 условия находятся мгновенно как -1 1
-- -n + n + 1 = 1
theorem ex4 (n : ℤ) : IsGCD(n, (n+1)) 1 := by
  unfold IsGCD
  constructor
  · constructor
    · exact one_dvd' n
    · exact one_dvd' (n+1)
  · use -1, 1
    ring
