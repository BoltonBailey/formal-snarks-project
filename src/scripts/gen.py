

vars = [
    "r_v", "r_w", "α_v", "α_w", "α_y", "β", "γ"]

monos = [
    (0, 0, 0, 0, 0, 0, 0),
    (1, 0, 0, 0, 0, 0, 0),
    (0, 1, 0, 0, 0, 0, 0),
    (1, 1, 0, 0, 0, 0, 0),
    (1, 0, 1, 0, 0, 0, 0),
    (0, 1, 0, 1, 0, 0, 0),
    (1, 1, 0, 0, 1, 0, 0),
    (1, 0, 0, 0, 0, 1, 0),
    (0, 1, 0, 0, 0, 1, 0),
    (1, 1, 0, 0, 0, 1, 0),
    (0, 0, 1, 0, 0, 0, 0),
    (0, 0, 0, 1, 0, 0, 0),
    (0, 0, 0, 0, 1, 0, 0),
    (0, 0, 0, 0, 0, 0, 1),
    (0, 0, 0, 0, 0, 1, 1)
]

counts = set()

for i in monos:
    for j in monos:
        k = tuple(i[n] + j[n] for n in range(7))
        counts.add(k)

counts.remove((0, 0, 0, 0, 0, 0, 0))

for roman in ["I", "II", "III", "IV", "V"]:
    for idx, count in enumerate(counts):
        line = f"have h{idx}eqn{roman} := congr_arg (coeff ("
        for var, n in zip(vars, count):
            if n > 0:
                line += f"single vars.{var} {n} + "
        line = line[:-3] + f")) eqn{roman}_verified,"

        print(line)
