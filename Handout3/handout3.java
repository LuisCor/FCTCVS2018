import java.util.Random;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
    predicate ProbeInv(Probe p;) =
       p.value |-> ?v &*&
       p.sensor |-> ?s &*&
       s != null &*&
       [_]SensorInv(s) &*&
       p.ran |-> ?r &*&
       r != null;
       
       
    predicate Sensor_frac(real r) = true;
@*/


class Probe implements Runnable
{
   //@ predicate pre() = ProbeInv(this);
   //@ predicate post() = true;


    int value = 0;

   
    
    SensorInt sensor;
    Random ran;
    TimeUnit t;
    

    public Probe(SensorInt sensor)
    //@ requires sensor != null &*& Sensor_frac(?f) &*& [f]SensorInv(sensor);
    //@ ensures pre();
    {
    	ran = new Random();
        this.sensor = sensor;
        //@ close pre();
        this.value = ran.nextInt(sensor.max - sensor.min + 1) + sensor.min;

    }



    public void run()
    //@ requires pre();
    //@ ensures post();
    {
    
        while( true )
        //@ invariant pre();
        {
           // produce a new value every 2 seconds
           value = ran.nextInt(sensor.max - sensor.min + 1) + sensor.min;
           sensor.set(value);          
           t.sleep(2000);
           //@ close post();
           
        }
    }

}



/*@
    predicate SensorInv(SensorInt s;) =
       s.mon |-> ?l &*&
       l != null &*&
       lck(l,1, Sensor_shared_state(s))
       ;
       
    predicate_ctor Sensor_shared_state (SensorInt s) () =
       s.value |-> ?v &*&
       s.max |-> ?max &*&
       s.min |-> ?min &*&
       max > min &*&
       max >= v &*&
       v >= min
       
    ;
@*/


class SensorInt
{

    //@ predicate pre() = SensorInv(this);
    //@ predicate post() = true;

    int value;
    int min;
    int max;
    
    Thread th;
    ReentrantLock mon;
    
    static final int SAMPLING = 3;
    
    SensorInt(int min, int max) 
    //@ requires max > min;
    //@ ensures SensorInv(this);
    {
        this.min = min;
        this.max = max;
        this.value = min;
        //@ close Sensor_shared_state(this)();
        //@ close enter_lck(1, Sensor_shared_state(this));
        this.mon = new ReentrantLock();

        //@ assert [1]SensorInv(this);
        
        //@ close Sensor_frac(1);
        while(true)
        //@ invariant Sensor_frac(?f) &*& [f]SensorInv(this);
        {
        //@ open Sensor_frac(f);
        //@ close Sensor_frac(f/2);
        this.th = new Thread(new Probe(this));
        //@close Sensor_frac(f/4);
        //@close Sensor_frac(f/4);
        this.th.start();
        }
        
        
    }
    
    
    int getMax()
    //@ requires SensorInv(this);
    //@ ensures true;
    { 
        return this.max;
    }  
    
    int getMin() 
    //@ requires SensorInv(this);
    //@ ensures true;    
    { 
        return this.min;
    }  
    
    int get() 
    { 
        return this.value;
    }    
    
    void set(int value)
    //@ requires [?f]SensorInv(this);
    //@ ensures [f]SensorInv(this); 
    {
    	//@open pre();
        mon.lock();
    	//@ open Sensor_shared_state(this)();
    
    	if(value > this.max)
    	    this.value = this.max;
    	else if(this.min > value)
    	    this.value = this.min;
    	else
    	    this.value = value;
    	//@ close Sensor_shared_state(this)();
    	mon.unlock();
    	//@ close SensorInv(this);    
		
    }
    
    public static void main(String args[]) throws InterruptedException
    {
        SensorInt s = new SensorInt(0,10);
        TimeUnit t;
        
        while(true)
        {
            // get and print a sample every 5 seconds
            System.out.println("Value: " + value);
            t.sleep(5000);
            
        }
    }
}

