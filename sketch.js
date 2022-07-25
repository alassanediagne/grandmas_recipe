var ta;
var tb;
const N = 10000; // number of iterations / points on the canvas
const zoom = 300;
var x = 0;
var y = 0;
var xb = 0;
var yb = -100;
var diameter = 30;
var dragging_ta;
var dragging_tb;
var ss_counter = 1;
var input1;
var input2;
var input3;
var input4;
var refresh;
var input_used = false;


// math functions for complex numbers and möbius transformations by Tim Hutton (https://github.com/timhutton/mobius-transforms/blob/7c035aa56447379aa66760577a8472e8b62fc064/code/math.js)


function p2( x, y ) { return { x:x, y:y, z:0 }; }
function p3( x, y, z ) { return { x:x, y:y, z:z }; }
function add( a, b ) { return p3( a.x + b.x, a.y + b.y, a.z + b.z ); }
function sub( a, b ) { return p3( a.x - b.x, a.y - b.y, a.z - b.z ); }
function mul( a, f ) { return p3( a.x * f, a.y * f, a.z * f ); }
function average( a, b ) { return mul( add( a, b ), 0.5 ); }
function dot( a, b ) { return a.x * b.x + a.y * b.y + a.z * b.z; }
function len2( a ) { return dot(a,a); }
function dist2( a, b ) { return len2( sub( a, b ) ); }
function dist( a, b ) { return Math.sqrt( len2( sub( a, b ) ) ); }
function mul_complex( a, b ) { return p2( a.x * b.x - a.y * b.y, a.y * b.x + a.x * b.y ); }
function div_complex( a, b ) { return p2( ( a.x * b.x + a.y * b.y ) / len2( b ), ( a.y * b.x - a.x * b.y ) / len2( b ) ); }
function negative( a ) { return p2( -a.x, -a.y ); }
function magnitude( a ) { return Math.sqrt( len2( a ) ); }
function normalize( a ) { return mul( a, 1 / magnitude( a ) ); }
function cross( a, b ) { return p3( a.y * b.z - a.z * b.y, a.z*b.x - a.x * b.z, a.x * b.y - a.y * b.x ); }
function phase( a ) { return Math.atan2( a.y, a.x ); }
function toPolar( a ) { return [ magnitude( a ), Math.atan2( a.y, a.x ) ]; }
function fromPolar( mag, phase ) { return p2( mag * Math.cos(phase), mag*Math.sin(phase) ) }
function sqrt_complex( a ) { return fromPolar( Math.sqrt( magnitude(a) ), phase(a) / 2.0 ); }
function complex_conjugate( p ) { return p2( p.x, -p.y ); }
function sphereInversion( p, sphere ) {
    var d2 = dist2( p, sphere.p );
    return add( sphere.p, mul( sub( p, sphere.p ), sphere.r * sphere.r / d2 ) );
}
function pow_complex( a, p ) {
    const [ r, theta ] = toPolar( a );
    return fromPolar( Math.pow( r, p ), theta * p );
}

function get_mobius_determinant( m ) {
    return sub( mul_complex( m[0], m[3] ), mul_complex( m[1], m[2] ) );
}

function mobius_normalize( m ) {
    // VCA, p.150
    var sqrt_ad_minus_bc = sqrt_complex( get_mobius_determinant( m ) );
    for( var i = 0; i < 4; i++ )
        m[i] = div_complex( m[i], sqrt_ad_minus_bc );
}


function get_mobius_inverse( m ) {
    return [m[3], mul(m[1], -1.0), mul(m[2], -1.0), m[0]];
}

function get_mobius_composed(...args) {
    return args.reduce((a, b) => {
        return [add(mul_complex(a[0], b[0]), mul_complex(a[1], b[2])),
                add(mul_complex(a[0], b[1]), mul_complex(a[1], b[3])),
                add(mul_complex(a[2], b[0]), mul_complex(a[3], b[2])),
                add(mul_complex(a[2], b[1]), mul_complex(a[3], b[3]))];
    });
}


function mobius_identity( m ) {
    m[0] = p2( 1, 0 );
    m[1] = p2( 0, 0 );
    m[2] = p2( 0, 0 );
    m[3] = p2( 1, 0 );
}

function mobius_on_point( m, z ) {
    if( isNaN(z.x) || isNaN(z.y) ) {
        // special case for z = inf, return a / c
        return div_complex( m[0], m[2] );
    }
    return div_complex( add( mul_complex( m[0], z ), m[1] ), add( mul_complex( m[2], z ), m[3] ) );
}

function get_mobius_trace( m ) {
    return add( m[0], m[3] );
}

function get_mobius_fixed_points( T ) {
    // Indra's Pearls, p. 84, p. 78
    // returns [ Fix+, Fix- ] (may be the same)
    var m = [ T[0], T[1], T[2], T[3] ];
    mobius_normalize( m );
    var TrT = get_mobius_trace( m );
    var T2 = get_mobius_composed( m, m );
    var TrT2 = get_mobius_trace( T2 );
    var n = mul( add( TrT, sqrt_complex( sub( TrT2, p2( 4.0, 0.0 ) ) ) ), 0.5 );
    var k = mul_complex( n, n );
    var st2p4 = sqrt_complex( sub( mul_complex( TrT, TrT ), p2( 4.0, 0.0 ) ) );
    var z_plus = div_complex( add( sub( m[0], m[3] ), st2p4 ), mul( m[2], 2.0 ) );
    var z_minus = div_complex( sub( sub( m[0], m[3] ), st2p4 ), mul( m[2], 2.0 ) );
    if( magnitude( k ) > 1.0 ) { return [ z_plus, z_minus ]; }
    else { return [ z_minus, z_plus ]; }
}

function complex_solve_quadratic( a, b, c ) {
    // return both solutions of ax^2 + bx + c = 0
    var sqrt_term = sqrt_complex( sub( mul_complex( b, b ), mul( mul_complex( a, c ), 4.0 ) ) );
    var x1 = div_complex( add( mul( b, -1.0 ), sqrt_term ),  mul( a, 2.0 ) );
    var x2 = div_complex( sub( mul( b, -1.0 ), sqrt_term ),  mul( a, 2.0 ) );
    return [ x1, x2 ];
}



/////////////////////


function setup() {
  createCanvas(1000, 1150);
  frameRate(24);
  background(0);
  setup_input();
}

function draw() {
  translate(width/2, height/2);
  fill(255);
  drag_ta();
  drag_tb();
  let gens = granny(ta,tb)[0];
  let inv = granny(ta, tb)[1];
  ifs(gens, inv, N);
}

function complex_matmul(a,b){
  return [add(mul_complex(a[0],b[0]),mul_complex(a[1],b[2])), add(mul_complex(a[0],b[1]),mul_complex(a[1],b[3])), add(mul_complex(a[2],b[0]),mul_complex(a[3],b[2])), add(mul_complex(a[2],b[1]), mul_complex(a[3],b[3]))];
}


function granny(ta, tb){
  let p = mul_complex(ta, tb);
  let q = add(pow_complex(ta,2),pow_complex(tb,2));
  let tab = complex_solve_quadratic(p2(1,0),negative(p),q)[1];
  let z0 = div_complex(mul_complex(sub(tab, p2(2,0)), tb), add(sub(mul_complex(tb, tab), mul_complex(p2(2,0), ta)), mul_complex(p2(0,2), tab)));
  let b = [div_complex(sub(tb, p2(0,2)), p2(2,0)), div_complex(tb, p2(2,0)), div_complex(tb, p2(2,0)), div_complex(add(tb, p2(0,2)), p2(2,0))];
  let ab = [div_complex(tab, p2(2,0)), div_complex(sub(tab, p2(2,0)), mul_complex(p2(2,0), z0)), div_complex(mul_complex(add(tab, p2(2,0)), z0), p2(2,0)), div_complex(tab, p2(2,0))];
  let B = get_mobius_inverse(b);
  let a = complex_matmul(ab, B);
  let A = get_mobius_inverse(a)
  var gens = [a,A,b,B];
  var inv = [1,0,3,2];
  return [gens, inv];
}

function ifs(gens, inv, N){
    let colours = ['rgb(0,255,127)', 'rgb(32,178,170)', 'rgb(127,255,212)', 'rgb(255,248,220)']; // colors for every point in the big disks Da,Db,DA,DB
    let fix = [];
    for (i = 0; i < 4; i++){
        fix[i] = get_mobius_fixed_points(gens[i]);
    }
    let r = random([0,1,2,3]);
    let z = fix[r];
    let T = gens[r];
    for(let i = 0; i < N; i++){
        let oldr = r;
        r = random([0,1,2,3]);
        if (inv[oldr] != r){
            T = complex_matmul(gens[r],T);
            z = mobius_on_point(T, z);
        }
        if(i>=200){
            stroke(colours[r]);
            point(z.x*zoom,-z.y*zoom);
            stroke(0);
        }
        
    }
}



function drag_ta(){
    if (input_used){ // sometimes the y coordinate needs a minus since the y axis in p5.js goes from top to bottom
        ta = p2(x/200+2, y/200);
    } 
    else{
        ta = p2(x/200+2, -y/200);
    }
    if (mouseIsPressed && dist(x, y, mouseX-width/2, mouseY-height/2) < diameter){
        dragging_ta = true;
        input_used = false;
    }
    else{
        dragging_ta = false;
    }
    if(dragging_ta){
        x = mouseX-width/2;
        y = mouseY-height/2;
        ta = p2(x/200+2, -y/200);
        background(0);
      }
    fill(200);
    rect(-500,500,1000,200);
    fill(0);
    textSize(25);
    text("ta = ", 30-width/2,1120-height/2);
    text(" + i * ", 170-width/2,1120-height/2);
    text("tb = ", 450-width/2,1120-height/2);
    text(" + i * ", 590-width/2,1120-height/2);
    fill(255)
    stroke(255);
    if (input_used){
        circle(x,-y,diameter);
        textSize(20);
        fill(0);
        text("ta", x-diameter/4, -y+diameter/4);
    }
    else{
        circle(x,y,diameter);
        textSize(20);
        fill(0);
        text("ta", x-diameter/4, y+diameter/4);
    }
    textSize(30);
    stroke(0);
    fill(255);
    if(ta.y >= 0){
        text("ta = " + three_decimals(ta.x).toString() + " + i * " + three_decimals(ta.y).toString(),200,350);
    }
    else{
        text("ta = " + three_decimals(ta.x).toString() + " - i * " + three_decimals(abs(ta.y).toString()),200,350);
    }
}

function drag_tb(){
    if (input_used){ 
        tb = p2(xb/200+2, yb/200);
    } 
    else{
        tb = p2(xb/200+2, -yb/200);
    }
    if (mouseIsPressed && dist(xb, yb, mouseX-width/2, mouseY-height/2) < diameter){
        dragging_tb = true;
        input_used = false;
    }
    else{
        dragging_tb = false;
    }
    if(dragging_tb && !dragging_ta){
        xb = mouseX-width/2;
        yb = mouseY-height/2;
        tb = p2(xb/200+2, -yb/200);
        background(0);
      }
    fill(200);
    rect(-500,500,1000,200);
    fill(0);
    textSize(25);
    text("ta = ", 30-width/2,1120-height/2);
    text(" + i * ", 170-width/2,1120-height/2);
    text("tb = ", 450-width/2,1120-height/2);
    text(" + i * ", 590-width/2,1120-height/2);
    stroke(255);
    fill(255);
    if (input_used){
        circle(xb,-yb,diameter);
        textSize(20);
        fill(0);
        text("tb", xb-diameter/4, -yb+diameter/4);
    }
    else{
        circle(xb,yb,diameter);
        textSize(20);
        fill(0);
        text("tb", xb-diameter/4, yb+diameter/4);
    }
    textSize(30);
    stroke(0);
    fill(255);
    if(tb.y >= 0){
        text("tb = " + three_decimals(tb.x).toString() + " + i * " + three_decimals(tb.y).toString(),200,400);
    }
    else{
        text("tb = " + three_decimals(tb.x).toString() + " - i * " + three_decimals(abs(tb.y)).toString(),200,400);
    }
}

function three_decimals(x){
    return Math.round(x*1000)/1000;
}

function keyTyped() {
    if (key === 's') {
      saveCanvas('grandmas_recipe_' + ss_counter.toString(), 'png');
      ss_counter++;
    }
}

function setup_input(){
  fill(0);
  textSize(25);
  input1 = createInput();
  input1.position(80,1100);
  input1.size(80);
  refresh = createButton("refresh");
  refresh.position(900,1100);
  refresh.mousePressed(read_input);
  input2 = createInput();
  input2.position(230,1100);
  input2.size(80);
  input3 = createInput();
  input3.position(500,1100);
  input3.size(80);
  input4 = createInput();
  input4.position(650,1100);
  input4.size(80);
}


function read_input(){
    input_used = true;
    x = (input1.value()-2)*200;
    y = (input2.value())*200;
    xb = (input3.value()-2)*200;
    yb = (input4.value())*200;
    ta = p2(x/200+2, y/200);
    tb = p2(x/200+2, y/200);
    background(0);
}