
/*@
    predicate SensorInv(SensorInt s; int m, int n) =
       s.value |-> ?v &*&
       s.max |-> m &*&
       s.min |-> n &*&
       m > n;
@*/


class SensorInt
{
    int value;
    int min;
    int max;
    
    Thread th;
    
    static final int SAMPLING = 3;
    
    SensorInt(int min, int max) 
    {
        this.min = min;
        this.max = max;
        this.value = min;
        this.th = new Thread(new Probe(this));
        this.th.start();
    }
    
    
    int getMax()
    //@ requires SensorInv(this, ?max, ?min);
    //@ ensures SensorInv(this, max, min);
    { 
        return this.max;
    }  
    
    int getMin() 
    //@ requires SensorInv(this, ?max, ?min);
    //@ ensures SensorInv(this, max, min);    
    { 
        return this.min;
    }  
    
    int get() 
    { 
        return this.value;
    }    
    
    void set(int value) 
    {
        this.value = value;
    }
    
    public static void main(String args[]) throws InterruptedException 
    ////@ requires System_out(?o) &*& o != null; 
    ////@ ensures true;
    //This needs to be enabled for the prints to work, but this is being a bitch and
    // it aint working
    {
        SensorInt s = new SensorInt(0,10);
        
        while(true)
        {
            // get and print a sample every 5 seconds
            System.out.println("Value: " + value);
            sleep(5000);
            
        }
    }
}