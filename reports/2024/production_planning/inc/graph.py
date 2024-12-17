import matplotlib.pyplot as plt
import numpy as np

time_years = [0, 2, 3.7]
production_units = [0, 27, 60]

interp_time = [1, 2, 3]
interp_units = np.interp(interp_time, time_years, production_units)

plt.figure(figsize=(8, 6))
plt.plot(time_years, production_units, marker='o', linestyle='-', color='blue', linewidth=2, label='Среднемесячный выпуск')

for i, t in enumerate(interp_time):
    plt.scatter(t, interp_units[i], color='red')
    plt.annotate(f"{interp_units[i]:.0f}", (t, interp_units[i]), textcoords="offset points", xytext=(0,5), ha='center')

for i, txt in enumerate(production_units):
    plt.annotate(f"{txt:.0f}", (time_years[i], production_units[i]), textcoords="offset points", xytext=(0,5), ha='center')

plt.title("Изменение среднемесячного выпуска изделий в период освоения")
plt.xlabel("t, лет")
plt.ylabel("N мес, шт/мес")
plt.grid(True)
plt.xticks(np.arange(0, 4.5, 0.5))  # Шаг оси X
plt.yticks(np.arange(0, 70, 10))  # Шаг оси Y
plt.legend()

plt.tight_layout()
plt.show()
