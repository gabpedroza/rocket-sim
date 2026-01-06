document.addEventListener('DOMContentLoaded', () => {
    // DOM Elements
    const canvas = document.getElementById('simulationCanvas');
    const ctx = canvas.getContext('2d');
    const altitudeDisplay = document.getElementById('altitude-display');
    const velocityDisplay = document.getElementById('velocity-display');
    const throttleDisplay = document.getElementById('throttle-display');
    const startButton = document.getElementById('start-button');
    const resetButton = document.getElementById('reset-button');
    const numInput = document.getElementById('controller-num');
    const denInput = document.getElementById('controller-den');
    const setpointTypeInput = document.getElementById('setpoint-type');
    const setpointValueInput = document.getElementById('setpoint-value');
    const disturbanceInput = document.getElementById('disturbance-magnitude');
    const speedSlider = document.getElementById('speed-slider');
    const gravityInput = document.getElementById('gravity-slider');
    const gravityValue = document.getElementById('gravity-value');
    const capThrustCheckbox = document.getElementById('cap-thrust');
    const controllerFormulaDiv = document.getElementById('controller-formula');
    const closedLoopFormulaDiv = document.getElementById('closed-loop-formula');
    const returnRatioFormulaDiv = document.getElementById('return-ratio-formula');
    const controllerBlockSpan = document.getElementById('controller-block');


    // Simulation State
    let simState = {
        running: false,
        lastTime: 0,
        accumulator: 0,
        animationFrameId: null,
    };
    
    // Constants
    const FIXED_DT = 0.005; // 5ms fixed physics step
    let G = 9.81; // Gravity m/s^2
    const ROCKET_MASS = 100; // kg
    let MAX_THRUST = ROCKET_MASS * G * 3; // Max thrust in Newtons
    const MAX_THROTTLE = 100; // %

    let rocket, controller;

    // --- Helper Functions for Control Theory ---

    function polyDiv(num, den) {
        // Removes leading zeros for accurate degree calculation
        while (num.length > 1 && Math.abs(num[0]) < 1e-9) num.shift();
        while (den.length > 1 && Math.abs(den[0]) < 1e-9) den.shift();

        if (den.length === 0 || (den.length === 1 && den[0] === 0)) {
            throw new Error("Denominator polynomial cannot be zero.");
        }

        let rem = [...num];
        if (rem.length < den.length) {
            return [[0], rem];
        }

        let quot = new Array(rem.length - den.length + 1).fill(0);
        
        for (let i = 0; i < quot.length; i++) {
            const coeff = rem[i] / den[0];
            quot[i] = coeff;
            for (let j = 0; j < den.length; j++) {
                rem[i + j] -= coeff * den[j];
            }
        }
        
        // Remove leading zeros from remainder for a clean result
        while (rem.length > 1 && Math.abs(rem[0]) < 1e-9) {
            rem.shift();
        }

        return [quot, rem];
    }

    function polyAdd(p1, p2) {
        const len1 = p1.length;
        const len2 = p2.length;
        const newLength = Math.max(len1, len2);
        const result = new Array(newLength).fill(0);
        for (let i = 0; i < newLength; i++) {
            const v1 = i < len1 ? p1[len1 - 1 - i] : 0;
            const v2 = i < len2 ? p2[len2 - 1 - i] : 0;
            result[newLength - 1 - i] = v1 + v2;
        }
        return result;
    }

    function polyMul(p1, p2) {
        if (!p1 || !p2 || p1.length === 0 || p2.length === 0) return [0];
        const result = new Array(p1.length + p2.length - 1).fill(0);
        for (let i = 0; i < p1.length; i++) {
            for (let j = 0; j < p2.length; j++) {
                result[i + j] += p1[i] * p2[j];
            }
        }
        return result;
    }

    function evaluateTF(num, den, s) {
        let numVal = new Complex(0, 0);
        for (let i = 0; i < num.length; i++) {
            const power = num.length - 1 - i;
            numVal = numVal.add(s.pow(power).mul(num[i]));
        }

        let denVal = new Complex(0, 0);
        for (let i = 0; i < den.length; i++) {
            const power = den.length - 1 - i;
            denVal = denVal.add(s.pow(power).mul(den[i]));
        }
        if (denVal.magnitude() === 0) return new Complex(Infinity, Infinity);
        return numVal.div(denVal);
    }
    
    function formatPoly(poly) {
        if (!poly || poly.length === 0) return "0";
        let str = "";
        for (let i = 0; i < poly.length; i++) {
            const p = poly.length - 1 - i;
            const c = poly[i];
            if (Math.abs(c) < 1e-6) continue;

            let cStr = Math.abs(c).toFixed(2).replace(/\.00$/, '');
            if (cStr === '1' && p !== 0) cStr = '';

            const sign = (c > 0) ? " + " : " - ";
            if (str === "" && c > 0) str = cStr;
            else str += sign + cStr;
            
            if (p > 0) str += "s";
            if (p > 1) str += `^${p}`;
        }
        return str.replace(/^ \+ /, '');
    }


    class Complex {
        constructor(re, im) { this.re = re; this.im = im; }
        add(c) { return new Complex(this.re + c.re, this.im + c.im); }
        mul(c) {
            if (typeof c === 'number') return new Complex(this.re * c, this.im * c);
            return new Complex(this.re * c.re - this.im * c.im, this.re * c.im + this.im * c.re);
        }
        div(c) {
            const den = c.re * c.re + c.im * c.im;
            if (den === 0) return new Complex(Infinity, Infinity);
            return new Complex((this.re * c.re + this.im * c.im) / den, (this.im * c.re - this.re * c.im) / den);
        }
        pow(p) {
            if (p === 0) return new Complex(1, 0);
            let result = this;
            for (let i = 1; i < p; i++) result = result.mul(this);
            return result;
        }
        magnitude() { return Math.sqrt(this.re * this.re + this.im * this.im); }
        phase() { return Math.atan2(this.im, this.re); }
    }


    // --- Classes ---

    class Rocket {
        constructor(y, v) {
            this.y = y; // altitude (m)
            this.v = v; // velocity (m/s)
            this.throttle = 0; // %
        }

        update(thrustCommand, disturbance, dt) {
            if (isNaN(dt) || dt > 0.5) return; // safety check

            if (capThrustCheckbox.checked) {
                this.throttle = Math.max(-MAX_THROTTLE, Math.min(MAX_THROTTLE, thrustCommand));
            } else {
                this.throttle = thrustCommand;
            }
            
            const thrustForce = (this.throttle / MAX_THROTTLE) * MAX_THRUST;
            
            const gravityForce = ROCKET_MASS * G;
            const disturbanceForce = (disturbance / 100) * MAX_THRUST * (Math.random() - 0.5) * 2;

            const totalForce = thrustForce - gravityForce + disturbanceForce;
            const acceleration = totalForce / ROCKET_MASS;

            this.v += acceleration * dt;
            this.y += this.v * dt;

            // Ground removed, no collision detection
        }

        draw(ctx, canvas) {
            ctx.clearRect(0, 0, canvas.width, canvas.height);



            // Rocket position
            const scale = (canvas.height - 40) / 200; // e.g., 200m visible range
            const rocketY = canvas.height - 20 - (this.y * scale);

            // Thrust Flame
            if (Math.abs(this.throttle) > 1) {
                const flameHeight = Math.abs(this.throttle) / MAX_THROTTLE * 30;
                ctx.fillStyle = this.throttle > 0 ? `rgba(255, 165, 0, ${0.5 + Math.random() * 0.5})` : `rgba(0, 165, 255, ${0.5 + Math.random() * 0.5})`;
                ctx.beginPath();
                ctx.moveTo(canvas.width / 2 - 5, rocketY);
                ctx.lineTo(canvas.width / 2 + 5, rocketY);
                ctx.lineTo(canvas.width / 2, rocketY + flameHeight);
                ctx.closePath();
                ctx.fill();
            }

            // Rocket Body
            ctx.fillStyle = '#d0d0d0';
            ctx.beginPath();
            ctx.moveTo(canvas.width / 2 - 10, rocketY);
            ctx.lineTo(canvas.width / 2 + 10, rocketY);
            ctx.lineTo(canvas.width / 2 + 10, rocketY - 40);
            ctx.lineTo(canvas.width / 2, rocketY - 55);
            ctx.lineTo(canvas.width / 2 - 10, rocketY - 40);
            ctx.closePath();
            ctx.fill();

            // Fins
            ctx.fillStyle = '#a0a0a0';
            ctx.beginPath();
            ctx.moveTo(canvas.width/2 - 10, rocketY - 10);
            ctx.lineTo(canvas.width/2 - 20, rocketY);
            ctx.lineTo(canvas.width/2 - 10, rocketY);
            ctx.closePath();
            ctx.fill();
            ctx.beginPath();
            ctx.moveTo(canvas.width/2 + 10, rocketY - 10);
            ctx.lineTo(canvas.width/2 + 20, rocketY);
            ctx.lineTo(canvas.width/2 + 10, rocketY);
            ctx.closePath();
            ctx.fill();
        }
    }
    
    class StateSpaceController {
        constructor(num, den) {
            // --- 1. Decompose into proper and improper parts ---
            const [quot, rem] = polyDiv(num, den);
            this.quot = quot;
            // History for input derivatives, max supported is 2nd order for simplicity
            this.input_history = new Array(2).fill(0); 
    
            // --- 2. Setup state-space for the strictly proper part: R(s)/D(s) ---
            const proper_num = rem;
            const proper_den = den;
    
            if (proper_den[0] === 0) throw new Error("Denominator's highest power cannot be zero.");
    
            const den_lead_coeff = proper_den[0];
            const den_norm = proper_den.map(d => d / den_lead_coeff);
            
            // Pad numerator to match denominator's degree for canonical form
            const num_padded = new Array(proper_den.length).fill(0);
            const offset = proper_den.length - proper_num.length;
            proper_num.forEach((n, i) => {
                if (i + offset >= 0) {
                     num_padded[i + offset] = n / den_lead_coeff;
                }
            });
            
            const n = den_norm.length - 1;
            if (n <= 0) { // System is just a gain
                this.A = []; this.B = []; this.C = [];
                this.D = (proper_num.length > 0 ? proper_num[0] : 0) / den_lead_coeff;
                this.x = [];
                return;
            }
    
            // --- 3. Controllable Canonical Form matrices ---
            this.A = Array(n).fill(0).map(() => Array(n).fill(0));
            this.B = Array(n).fill(0);
            
            for(let i=0; i<n; i++) this.A[0][i] = -den_norm[i+1];
            for(let i=1; i<n; i++) this.A[i][i-1] = 1;
            this.B[0] = 1;
    
            this.C = Array(n).fill(0);
            // D-term of proper part is 0 since deg(rem) < deg(den)
            const d_term_of_proper_part = num_padded[0]; 
            for(let i=0; i<n; i++) {
                this.C[i] = num_padded[i+1] - d_term_of_proper_part * den_norm[i+1];
            }
            this.D = d_term_of_proper_part; 
            this.x = Array(n).fill(0);
        }

        // Helper for RK4: Computes Ax + Bu
        stateDeriv(x, u) {
            const dx = new Array(x.length).fill(0);
            for(let i = 0; i < x.length; i++) {
                for(let j = 0; j < x.length; j++) {
                    dx[i] += this.A[i][j] * x[j];
                }
                dx[i] += this.B[i] * u;
            }
            return dx;
        }

        // Vector Helpers
        vecAdd(v1, v2) { return v1.map((val, i) => val + v2[i]); }
        vecScale(v, s) { return v.map(val => val * s); }
    
        update(input, dt) {
            // --- 1. Calculate output from proper part R(s)/D(s) ---
            let proper_output = 0;
            if (this.A.length > 0) {
                if (dt > 1e-9) {
                    // RK4 Integration
                    const k1 = this.stateDeriv(this.x, input);
                    const k2 = this.stateDeriv(this.vecAdd(this.x, this.vecScale(k1, dt/2)), input);
                    const k3 = this.stateDeriv(this.vecAdd(this.x, this.vecScale(k2, dt/2)), input);
                    const k4 = this.stateDeriv(this.vecAdd(this.x, this.vecScale(k3, dt)), input);

                    // x_new = x + dt/6 * (k1 + 2k2 + 2k3 + k4)
                    const delta = this.vecScale(
                        this.vecAdd(
                            this.vecAdd(k1, k4),
                            this.vecScale(this.vecAdd(k2, k3), 2)
                        ),
                        dt / 6
                    );
                    this.x = this.vecAdd(this.x, delta);
                }
                
                let output_from_C = 0;
                for (let i = 0; i < this.x.length; i++) {
                    output_from_C += this.C[i] * this.x[i];
                }
                proper_output = output_from_C + this.D * input;
            } else {
                proper_output = this.D * input; // Case where den is constant
            }
    
            // --- 2. Calculate output from improper part Q(s) ---
            let improper_output = 0;
            const q_poly = this.quot;
            const q_deg = q_poly.length - 1;
            const [u_prev, u_prev2] = this.input_history;
            const safe_dt = dt > 1e-9 ? dt : 1e-9;
            
            // Zeroth derivative: q_n * u(t)
            if (q_deg >= 0) improper_output += q_poly[q_deg] * input;
            
            // First derivative: q_{n-1} * u'(t)
            if (q_deg >= 1) {
                const u_dot = (input - u_prev) / safe_dt;
                improper_output += q_poly[q_deg - 1] * u_dot;
            }
            
            // Second derivative: q_{n-2} * u''(t)
            if (q_deg >= 2) {
                const u_dot = (input - u_prev) / safe_dt;
                const u_dot_prev = (u_prev - u_prev2) / safe_dt;
                const u_ddot = (u_dot - u_dot_prev) / safe_dt;
                improper_output += q_poly[q_deg - 2] * u_ddot;
            }
            // Higher orders can be added here if needed
    
            // --- 3. Update history and return total output ---
            this.input_history[1] = u_prev;
            this.input_history[0] = input;
            
            return proper_output + improper_output;
        }
    
        reset() { 
            this.x.fill(0); 
            this.input_history.fill(0);
        }
    }


    // --- Main Functions ---

    function init() {
        resizeCanvas();
        rocket = new Rocket(100, 0); // Start at 100m altitude, 0 velocity
        updateController();
        updateUI();
        updatePlots();
        rocket.draw(ctx, canvas);
    }

    function reset() {
        if (simState.running) startStop();
        init();
    }
    
    function startStop() {
        simState.running = !simState.running;
        startButton.textContent = simState.running ? 'Stop' : 'Start';
        startButton.style.backgroundColor = simState.running ? 'var(--red-color)' : 'var(--green-color)';

        if (simState.running) {
            simState.lastTime = performance.now();
            updateController(); // re-read params on start
            if(controller) controller.reset();
            mainLoop(simState.lastTime);
        } else {
            if (simState.animationFrameId) cancelAnimationFrame(simState.animationFrameId);
        }
    }

    function mainLoop(currentTime) {
        if (!simState.running || !controller) return;

        const simSpeed = parseFloat(speedSlider.value);
        let frameDt = (currentTime - simState.lastTime) / 1000 * simSpeed;
        simState.lastTime = currentTime;

        // Cap frameDt to prevent explosion on tab switch or lag
        if (frameDt > 0.1) frameDt = 0.1;

        simState.accumulator += frameDt;

        const setpointValue = parseFloat(setpointValueInput.value);
        const disturbance = parseFloat(disturbanceInput.value);

        while (simState.accumulator >= FIXED_DT) {
            // Get current error based on latest physics state
            const currentValue = setpointTypeInput.value === 'altitude' ? rocket.y : rocket.v;
            const error = setpointValue - currentValue;
            
            // Update Controller inside the physics loop (Higher frequency)
            const thrustCommand = controller.update(error, FIXED_DT);

            // Feedforward Gravity Compensation
            const hoverThrottle = (ROCKET_MASS * G) / MAX_THRUST * 100;
            const totalCommand = thrustCommand + hoverThrottle;

            // Update Rocket Physics
            rocket.update(totalCommand, disturbance, FIXED_DT);

            simState.accumulator -= FIXED_DT;
        }
        
        updateUI();
        rocket.draw(ctx, canvas);

        simState.animationFrameId = requestAnimationFrame(mainLoop);
    }
    
    function updateUI() {
        altitudeDisplay.textContent = rocket.y.toFixed(2);
        velocityDisplay.textContent = rocket.v.toFixed(2);
        throttleDisplay.textContent = rocket.throttle.toFixed(1);
    }

    function updateController() {
         try {
            const num = parsePolyInput(numInput.value);
            const den = parsePolyInput(denInput.value);
            controller = new StateSpaceController(num, den);
        } catch (e) {
            alert('Error initializing controller: ' + e.message);
            controller = null;
        }
    }

    function findPolyRoots(poly) {
        // Durand-Kerner method for finding polynomial roots
        const n = poly.length - 1;
        if (n < 1) return [];

        // Normalize the polynomial
        const a = poly.map(c => new Complex(c / poly[0], 0));
        
        let roots = [];
        // Initial guess for roots
        let p = new Complex(0.4, 0.9);
        for(let i=0; i < n; i++) {
            roots.push(p.pow(i));
        }

        const evaluatePoly = (p, x) => {
            let result = new Complex(0,0);
            for(let i=0; i<p.length; i++) {
                result = result.add(x.pow(p.length - 1 - i).mul(p[i]));
            }
            return result;
        };

        for(let iter = 0; iter < 500; iter++) {
            let max_delta = 0;
            let next_roots = [];
            for (let i = 0; i < n; i++) {
                let p_i = roots[i];
                let numerator = evaluatePoly(a, p_i);
                let denominator = new Complex(1,0);
                for (let j = 0; j < n; j++) {
                    if (i === j) continue;
                    denominator = denominator.mul(p_i.add(roots[j].mul(-1)));
                }
                
                const delta = numerator.div(denominator);
                next_roots[i] = p_i.add(delta.mul(-1));
                if(delta.magnitude() > max_delta) max_delta = delta.magnitude();
            }
            roots = next_roots;
            if(max_delta < 1e-9) break;
        }
        return roots;
    }

    function formatRoots(roots) {
        if (!roots || roots.length === 0) return 'No roots found.';
        return roots.map(root => {
            const re = root.re.toFixed(3);
            const im = root.im.toFixed(3);
            if (Math.abs(root.im) < 1e-4) return re;
            return `${re} &pm; ${Math.abs(im)}i`;
        }).join(', ');
    }

    function getUniquePolesWithMultiplicity(roots) {
        const unique = [];
        const tolerance = 1e-5; // Tolerance for grouping poles

        roots.forEach(root => {
            let found = false;
            for (let u of unique) {
                const dist = Math.sqrt(Math.pow(u.re - root.re, 2) + Math.pow(u.im - root.im, 2));
                if (dist < tolerance) {
                    u.count++;
                    // Average the position to center it
                    u.re = (u.re * (u.count - 1) + root.re) / u.count;
                    u.im = (u.im * (u.count - 1) + root.im) / u.count;
                    found = true;
                    break;
                }
            }
            if (!found) {
                unique.push({ re: root.re, im: root.im, count: 1 });
            }
        });
        return unique;
    }

    function unwrapPhase(phases) {
        if (phases.length === 0) return [];
        const unwrapped = [phases[0]];
        for (let i = 1; i < phases.length; i++) {
            let diff = phases[i] - phases[i - 1];
            while (diff > 180) diff -= 360;
            while (diff < -180) diff += 360;
            unwrapped.push(unwrapped[i - 1] + diff);
        }
        return unwrapped;
    }

    function updatePlots() {
        try {
            const numC = parsePolyInput(numInput.value);
            const denC = parsePolyInput(denInput.value);
             if (denC.every(c => c===0) ) {
                return; // Invalid TF if den is all zeros
            }
            const plantGain = (G * 3) / MAX_THROTTLE;
            let numP, denP;

            if (setpointTypeInput.value === 'altitude') {
                numP = [plantGain];
                denP = [1, 0, 0];
            } else { // velocity
                numP = [plantGain];
                denP = [1, 0];
            }
            
            const numL = polyMul(numC, numP);
            const denL = polyMul(denC, denP);

            const numT = numL;
            const denT = polyAdd(denL, numL);

            controllerFormulaDiv.innerHTML = `<sup>${formatPoly(numC)}</sup>&frasl;<sub>${formatPoly(denC)}</sub>`;
            closedLoopFormulaDiv.innerHTML = `<sup>${formatPoly(numT)}</sup>&frasl;<sub>${formatPoly(denT)}</sub>`;
            if (returnRatioFormulaDiv) {
                 returnRatioFormulaDiv.innerHTML = `<sup>${formatPoly(numL)}</sup>&frasl;<sub>${formatPoly(denL)}</sub>`;
            }

            const roots = findPolyRoots(denT);
            const rootsL = findPolyRoots(denL);
            
            // Group poles for display
            const uniquePoles = getUniquePolesWithMultiplicity(roots);
            const uniquePolesL = getUniquePolesWithMultiplicity(rootsL);

            const polesLayout = {
                title: 'System Poles',
                xaxis: { title: 'Real Part', zeroline: true, zerolinecolor: '#666', gridcolor: '#444' },
                yaxis: { title: 'Imaginary Part', scaleanchor: "x", scaleratio: 1, zeroline: true, zerolinecolor: '#666', gridcolor: '#444' },
                paper_bgcolor: 'var(--primary-color)', plot_bgcolor: 'var(--secondary-color)',
                font: { color: 'var(--font-color)' }, showlegend: true,
                legend: { x: 1, xanchor: 'right', y: 1 },
                margin: { t: 40, b: 40, l: 40, r: 40 }
            };
            
            Plotly.newPlot('poles-plot', [
                {
                    x: uniquePoles.map(p => p.re),
                    y: uniquePoles.map(p => p.im),
                    text: uniquePoles.map(p => p.count > 1 ? p.count.toString() : ''),
                    textposition: 'bottom right',
                    type: 'scatter',
                    mode: 'markers+text',
                    name: `Closed-Loop Poles (${roots.length})`,
                    marker: { size: 10, color: '#00ff88', symbol: 'x-thin', line: {width: 3} },
                    textfont: { size: 14, color: '#00ff88' },
                    hovertemplate: 'Real: %{x:.3f}<br>Imag: %{y:.3f}<br>Multiplicity: %{text}<extra>Closed-Loop</extra>'
                },
                {
                    x: uniquePolesL.map(p => p.re),
                    y: uniquePolesL.map(p => p.im),
                    text: uniquePolesL.map(p => p.count > 1 ? p.count.toString() : ''),
                    textposition: 'top right',
                    type: 'scatter',
                    mode: 'markers+text',
                    name: `Return Ratio Poles (${rootsL.length})`,
                    marker: { size: 10, color: '#ffaa00', symbol: 'circle-open', line: {width: 2} },
                    textfont: { size: 14, color: '#ffaa00' },
                    hovertemplate: 'Real: %{x:.3f}<br>Imag: %{y:.3f}<br>Multiplicity: %{text}<extra>Return Ratio</extra>'
                }
            ], polesLayout);

            const frequencies = [], magnitudes = [], phases = [], nyquistReal = [], nyquistImag = [];
            for (let i = -2; i <= 4; i += 0.02) { // Smaller step for more points
                const w = Math.pow(10, i);
                frequencies.push(w);
                const s = new Complex(0, w);

                const responseT = evaluateTF(numT, denT, s);
                magnitudes.push(20 * Math.log10(responseT.magnitude()));
                phases.push(responseT.phase() * 180 / Math.PI);

                const responseL = evaluateTF(numL, denL, s);
                nyquistReal.push(responseL.re);
                nyquistImag.push(responseL.im);
            }

            const unwrappedPhases = unwrapPhase(phases);

            const minFrequency = Math.min(...frequencies);
            const maxFrequency = Math.max(...frequencies);
            
            const bodeLayout = {
                title: 'Closed-Loop Bode Plot',
                xaxis: { type: 'log', title: 'Frequency (rad/s)'},
                yaxis: { title: 'Magnitude (dB)'},
                xaxis2: { type: 'log', anchor: 'y', title: 'Frequency (rad/s)' },
                yaxis2: { title: 'Phase (deg)', side: 'right' },
                grid: { rows: 2, columns: 1, pattern: 'independent' },
                paper_bgcolor: 'var(--primary-color)', plot_bgcolor: 'var(--secondary-color)',
                font: { color: 'var(--font-color)' }, showlegend: false
            };
            Plotly.newPlot('bodePlot', [
                { x: frequencies, y: magnitudes, type: 'scatter', name: 'Magnitude' },
                { x: frequencies, y: unwrappedPhases, type: 'scatter', name: 'Phase', xaxis: 'x2', yaxis: 'y2'}
            ], bodeLayout);

            const nyquistLayout = {
                title: 'Nyquist Plot of Return Ratio L(s) = C(s)P(s)',
                xaxis: { title: 'Real Part', scaleanchor: "y", scaleratio: 1 },
                yaxis: { title: 'Imaginary Part' },
                paper_bgcolor: 'var(--primary-color)', plot_bgcolor: 'var(--secondary-color)',
                font: { color: 'var(--font-color)' }, showlegend: false
            };


            Plotly.newPlot('nyquistPlot', [{
                x: nyquistReal,
                y: nyquistImag.map(v => -v),
                type: 'scatter',
                mode: 'lines',
                line: {
                    color: 'rgba(100, 149, 237, 0.5)', // Cornflower blue, semi-transparent
                    width: 2,
                    dash: 'dot'
                },
                name: 'L(-jω) (Negative Freq)'
            }, {
                x: nyquistReal,
                y: nyquistImag,
                type: 'scatter', // Reverted to scatter
                mode: 'lines',
                line: {
                    color: 'blue', // Static color for the main line
                    width: 2
                },
                name: 'L(jω) (Positive Freq)'
            }, {
                x: nyquistReal,
                y: nyquistImag,
                type: 'scatter',
                mode: 'markers', // Markers will be visible
                marker: {
                    size: 8, // Increased size for visibility
                    color: frequencies, // Use frequencies to color the markers
                    colorscale: 'Jet', // A good contrasting colorscale
                    showscale: true, // Show the color scale legend
                    colorbar: {
                        title: 'Frequency (rad/s)',
                        titleside: 'right',
                        x: 1.05, // Position the colorbar slightly to the right of the plot
                        y: 0.5,
                        len: 0.5, // Length of the colorbar
                        thickness: 15,
                        tickfont: { color: 'var(--font-color)' },
                        titlefont: { color: 'var(--font-color)' }
                    }
                },
                text: frequencies.map(f => `Freq: ${f.toPrecision(3)} rad/s`), // Custom text for hover
                hoverinfo: 'text', // Show custom text on hover
                name: 'Frequency Markers'
            }, {
                x: [-1], // x-coordinate for the critical point
                y: [0],  // y-coordinate for the critical point
                type: 'scatter',
                mode: 'markers',
                marker: {
                    color: 'red',
                    size: 15, // Make it a big blob
                    symbol: 'circle' // Use a circle symbol for the blob
                },
                name: 'Critical Point (-1, 0)'
            }], nyquistLayout);

        } catch (e) {
            console.error("Could not update plots:", e);
        }
    }
    
    function parsePolyInput(value) {
        if (!value.trim()) return [0];
        return value.split(',').map(s => {
            const num = parseFloat(s.trim());
            if (isNaN(num)) throw new Error('Invalid number in polynomial input');
            return num;
        });
    }

    function resizeCanvas() {
        const dpr = window.devicePixelRatio || 1;
        const rect = canvas.getBoundingClientRect();
        canvas.width = rect.width * dpr;
        canvas.height = rect.height * dpr;
    }
    
    // --- Event Listeners ---
    
    window.addEventListener('resize', () => {
        resizeCanvas();
        updatePlots();
        if (rocket) rocket.draw(ctx, canvas);
    });

    startButton.addEventListener('click', startStop);
    resetButton.addEventListener('click', reset);
    numInput.addEventListener('change', () => { updateController(); updatePlots(); });
    denInput.addEventListener('change', () => { updateController(); updatePlots(); });
    setpointTypeInput.addEventListener('change', updatePlots);
    gravityInput.addEventListener('input', () => {
        G = parseFloat(gravityInput.value);
        MAX_THRUST = ROCKET_MASS * G * 3;
        gravityValue.textContent = G.toFixed(2);
        updatePlots();
    });

    // --- Initialization ---
    init();
});
